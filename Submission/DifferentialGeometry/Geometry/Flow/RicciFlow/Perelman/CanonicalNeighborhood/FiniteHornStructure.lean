import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedBoundedCurvature
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedTerminalDerivatives
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CurvatureEscape
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornDefs
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornEndGeometryDepth
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupConvergence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ConeConvergence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ConeTerminalExclusion
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornDirectionCompactness
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornEndpoint
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornEndAngleMonotone
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornIntrinsicRays
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornRayApproximation
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornTwoScale
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalParabolicBounds
import Mathlib.Topology.MetricSpace.Completion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open scoped _root_.Topology _root_.Submission.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W] [SigmaCompactSpace W]

attribute [local instance] FiniteHorn.ambient_metric
attribute [local instance] EndAngles.metric

structure AmbientEndIsometry {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g) : Prop where
  deep : ∃ i, (∀ x ∈ H.subend i, ∀ y ∈ H.subend i,
      _root_.Dist.dist x y = _root_.Dist.dist (H.inclusion x) (H.inclusion y)) ∧
    ∀ x ∈ H.subend i, _root_.Dist.dist (x : UniformSpace.Completion W) H.endpoint =
      _root_.Dist.dist (H.inclusion x) H.ambient_end

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.AmbientEndIsometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.AmbientEndIsometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.AmbientEndIsometry ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.AmbientEndIsometry

omit [SigmaCompactSpace W] in
theorem finiteHorn_ambientEndIsometry {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g) :
    AmbientEndIsometry H :=
  ⟨H.ambient_end_isometry⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_ambientEndIsometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_ambientEndIsometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_ambientEndIsometry ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_ambientEndIsometry

omit [SigmaCompactSpace W] in
theorem finiteHorn_frontier_escape_of_ambientEndIsometry {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (hiso : AmbientEndIsometry H) :
    ∀ w : ℕ → W,
      Filter.Tendsto (fun i => (w i : UniformSpace.Completion W)) Filter.atTop
        (nhds H.endpoint) →
      ∀ R : ℝ, 0 < R → ∀ᶠ i in Filter.atTop, ∀ z ∈ H.outer_frontier,
        R * _root_.Dist.dist (w i : UniformSpace.Completion W) H.endpoint < _root_.Dist.dist (H.inclusion (w i)) z := by
  obtain ⟨i₀, -, hdist⟩ := hiso.deep
  obtain ⟨δ, hδ, hfar⟩ := H.frontier_far
  intro w hw R hR
  have hmem : ∀ᶠ i in Filter.atTop, w i ∈ H.subend i₀ :=
    finiteHorn_eventually_mem_subend g H hw i₀
  have hsmall : ∀ᶠ i in Filter.atTop,
      dist (w i : UniformSpace.Completion W) H.endpoint < δ / (R + 1) := by
    have hpos : 0 < δ / (R + 1) := div_pos hδ (by linarith)
    exact hw.eventually (Metric.ball_mem_nhds H.endpoint hpos)
  filter_upwards [hmem, hsmall] with i hi hsi
  intro z hz
  have hzδ : δ ≤ _root_.Dist.dist z H.ambient_end := hfar z hz
  have hri : _root_.Dist.dist (w i : UniformSpace.Completion W) H.endpoint =
      dist (H.inclusion (w i)) H.ambient_end := hdist (w i) hi
  have hkey : δ - _root_.Dist.dist (w i : UniformSpace.Completion W) H.endpoint ≤
      dist z (H.inclusion (w i)) := by
    have h := abs_dist_sub_le z (H.inclusion (w i)) H.ambient_end
    rw [← hri] at h
    have := (abs_le.mp h).2
    linarith
  have hexpand : R * _root_.Dist.dist (w i : UniformSpace.Completion W) H.endpoint <
      δ - _root_.Dist.dist (w i : UniformSpace.Completion W) H.endpoint := by
    have h := (lt_div_iff₀ (by linarith : (0 : ℝ) < R + 1)).mp hsi
    nlinarith
  rw [dist_comm (H.inclusion (w i)) z]
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_frontier_escape_of_ambientEndIsometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_frontier_escape_of_ambientEndIsometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_frontier_escape_of_ambientEndIsometry ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_frontier_escape_of_ambientEndIsometry

theorem finite_horn_end_rays_of_ambientEndIsometry {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (hiso : AmbientEndIsometry H) : Nonempty (EndGeometry H) :=
  ⟨{ unique_endpoint := finiteHorn_unique_endpoint g H
     intrinsic_ambient := hiso.deep
     rays := finiteHorn_intrinsic_rays g H
     frontier_escape := finiteHorn_frontier_escape_of_ambientEndIsometry H hiso }⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_end_rays_of_ambientEndIsometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_end_rays_of_ambientEndIsometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_end_rays_of_ambientEndIsometry ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_end_rays_of_ambientEndIsometry

theorem finite_horn_end_rays {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g) :
    Nonempty (EndGeometry H) :=
  finite_horn_end_rays_of_ambientEndIsometry H (finiteHorn_ambientEndIsometry H)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_end_rays then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_end_rays"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_end_rays ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_end_rays

theorem finite_horn_ray_approximation {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (_endData : EndGeometry H)
    (hdepth : hornEndGeometryDepth.{u} ≤ H.collar_depth) :
    ∃ d : ℝ, 0 < d ∧ ∀ a b : EndRay H.endpoint,
      ∀ lo hi : Fin 2 → ℝ, (∀ k, 0 < lo k) → (∀ k, lo k ≤ hi k) →
      hi 0 ≤ a.length → hi 1 ≤ b.length → (∀ k, hi k ≤ d) →
      Nonempty (RayApproximation H a b lo hi) := by
  obtain ⟨d, hd, happ⟩ := (hornEndGeometryDepth_spec W g H hdepth).1
  exact ⟨d, hd, fun a b lo hi hlo _ hia hib hid => happ a b lo hi hlo hia hib hid⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_ray_approximation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_ray_approximation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_ray_approximation ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_ray_approximation

theorem finite_horn_end_angle {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (_endData : EndGeometry H)
    (hdepth : hornEndGeometryDepth.{u} ≤ H.collar_depth) : Nonempty (EndAngles H) :=
  (hornEndGeometryDepth_spec W g H hdepth).2.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_end_angle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_end_angle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_end_angle ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_end_angle


omit [SigmaCompactSpace W] in
theorem finite_horn_direction_compactness {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (_endData : EndGeometry H) (angles : EndAngles H)
    (hnet : ScaleDirectionNet g H) (hsep : ScaleSeparatedEndRays g H) :
    letI := angles.metric
    TotallyBounded (Set.univ : Set angles.quotient) ∧
      CompactSpace (UniformSpace.Completion angles.quotient) ∧
      ∃ a b : EndRay H.endpoint, 0 < angles.angle a b := by
  have htb : TotallyBounded (Set.univ : Set angles.quotient) :=
    totallyBounded_quotient_of_scaleDirectionNet H angles hnet
  exact ⟨htb, Metric.compactSpace_completion_of_totallyBounded htb,
    exists_pos_angle_of_separatedEndRays H angles (separatedEndRays_of_scaleSeparated H angles hsep)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_direction_compactness then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_direction_compactness"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_direction_compactness ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_direction_compactness


theorem finite_horn_cone_convergence {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (_endData : EndGeometry H) (angles : EndAngles H)
    (ray : EndRay H.endpoint) (d : ℕ → ℝ) (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hreal : ConeDistanceRealization H angles ray d)
    (hdepth : hornEndGeometryDepth.{u} ≤ H.collar_depth) :
    Nonempty (AnnularConvergence H angles ray d) :=
  nonempty_annularConvergence_of_coneAnnulusRealization H angles ray d hd hzero
    (coneAnnulusRealization_of_coneDistanceRealization
      ((hornEndGeometryDepth_spec W g H hdepth).2.2 angles)
      hreal)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_cone_convergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_cone_convergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_cone_convergence ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_cone_convergence

omit [SigmaCompactSpace W] in
theorem nonempty_hornBarriers_of_neckSectionBarrier {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (ray : EndRay H.endpoint) (d : ℕ → ℝ)
    (barrier : NeckSectionBarrier H ray d) : Nonempty (HornBarriers H ray d) := by
  classical
  have hrange : ∀ i : ℕ, Set.range (fun p : Sphere 2 => (barrier.tube i).map (p, 1 / 2)) =
      (barrier.tube i).sectionSet (1 / 2) :=
    fun i => GlobalNeckTube.range_sectionMap (barrier.tube i) (1 / 2)
  refine ⟨{ sphere := fun i p => (barrier.tube i).map (p, 1 / 2)
            embedding := ?_
            smooth := ?_
            diameter_bound := ?_
            radial_barrier := ?_ }⟩
  · intro i
    have hmem : ∀ p : Sphere 2, (p, (1 / 2 : ℝ)) ∈ (barrier.tube i).map.source := by
      intro p
      rw [(barrier.tube i).source_eq]
      exact ⟨Set.mem_univ _, by norm_num⟩
    have hcont : Continuous (fun p : Sphere 2 => (barrier.tube i).map (p, 1 / 2)) := by
      exact ((barrier.tube i).map.contMDiffOn_toFun.continuousOn).comp_continuous
        (f := fun p : Sphere 2 => (p, (1 / 2 : ℝ))) (by fun_prop) (fun p => hmem p)
    have hinj : Function.Injective (fun p : Sphere 2 => (barrier.tube i).map (p, 1 / 2)) := by
      intro p q hpq
      have hp : (barrier.tube i).map.invFun
          ((barrier.tube i).map.toFun (p, (1 / 2 : ℝ))) = (p, (1 / 2 : ℝ)) :=
        (barrier.tube i).map.left_inv' (hmem p)
      have hq : (barrier.tube i).map.invFun
          ((barrier.tube i).map.toFun (q, (1 / 2 : ℝ))) = (q, (1 / 2 : ℝ)) :=
        (barrier.tube i).map.left_inv' (hmem q)
      have hpq' : (barrier.tube i).map.toFun (p, (1 / 2 : ℝ)) =
          (barrier.tube i).map.toFun (q, (1 / 2 : ℝ)) := hpq
      have h : (p, (1 / 2 : ℝ)) = (q, (1 / 2 : ℝ)) := by rw [← hp, hpq', hq]
      exact congrArg Prod.fst h
    exact (hcont.isClosedEmbedding hinj).isEmbedding
  · intro i
    have hmem : ∀ p : Sphere 2, (p, (1 / 2 : ℝ)) ∈ (barrier.tube i).map.source := by
      intro p
      rw [(barrier.tube i).source_eq]
      exact ⟨Set.mem_univ _, by norm_num⟩
    exact (barrier.tube i).map.contMDiffOn_toFun.comp_contMDiff
      (contMDiff_id.prodMk contMDiff_const) (fun p => hmem p)
  · obtain ⟨L, hL, hbound⟩ := barrier.section_diameter
    refine ⟨L, hL, ?_⟩
    filter_upwards [hbound] with i hi x hx
    exact hi x ((hrange i).symm ▸ hx)
  · intro eta heta heta'
    filter_upwards [barrier.separates eta heta heta'] with i hi c hc hd'
    obtain ⟨t, ht⟩ := hi c hc hd'
    exact ⟨t, (hrange i).symm ▸ ht⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_hornBarriers_of_neckSectionBarrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_hornBarriers_of_neckSectionBarrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_hornBarriers_of_neckSectionBarrier ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_hornBarriers_of_neckSectionBarrier

noncomputable def tailIndex (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g) : ℕ :=
  Classical.choose H.cylindrical_tail

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.tailIndex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.tailIndex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.tailIndex ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.tailIndex

omit [SigmaCompactSpace W] in
theorem tailIndex_spec (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g) :
    ∀ x ∈ H.subend (tailIndex g H), ∃ (cyl : CylinderReference)
      (F : PartialDiffeomorph IC I3 Cylinder W ∞) (p : Sphere 2),
      F (p, 0) = x ∧
      Nonempty (GlobalNeckCrossSection F H.subend H.axial.point H.axial.length) ∧
      Set.univ ×ˢ Set.Icc (-H.collar_depth) H.collar_depth ⊆ F.source ∧
      ∃ hQ : 0 < metricScalarAt g x,
        Nonempty (MetricComparisonOn (fun _ => cyl.metric 0)
          (fun _ => scaleMetric (metricScalarAt g x) hQ g) F
          (Set.univ ×ˢ Set.Icc (-H.collar_depth) H.collar_depth)
          {0} (⌈H.neck_precision⁻¹⌉₊) H.neck_precision) :=
  Classical.choose_spec H.cylindrical_tail

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.tailIndex_spec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.tailIndex_spec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.tailIndex_spec ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.tailIndex_spec

structure EndChart (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g) (x : W)
    (hx : x ∈ H.subend (tailIndex g H)) where
  cyl : CylinderReference
  F : PartialDiffeomorph IC I3 Cylinder W ∞
  p : Sphere 2
  center : F (p, 0) = x
  cross : GlobalNeckCrossSection F H.subend H.axial.point H.axial.length
  source_sub : Set.univ ×ˢ Set.Icc (-H.collar_depth) H.collar_depth ⊆ F.source
  Q_pos : 0 < metricScalarAt g x
  cmp : MetricComparisonOn (fun _ => cyl.metric 0)
    (fun _ => scaleMetric (metricScalarAt g x) Q_pos g) F
    (Set.univ ×ˢ Set.Icc (-H.collar_depth) H.collar_depth)
    {0} (⌈H.neck_precision⁻¹⌉₊) H.neck_precision

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndChart ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndChart

omit [SigmaCompactSpace W] in
noncomputable def endChart (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g) (x : W)
    (hx : x ∈ H.subend (tailIndex g H)) : EndChart g H x hx :=
  Classical.choice (show Nonempty (EndChart g H x hx) from by
    obtain ⟨cyl, F, p, hcenter, hG, hsource, hQ, hcmp⟩ := tailIndex_spec g H x hx
    obtain ⟨G⟩ := hG
    obtain ⟨cmp⟩ := hcmp
    exact ⟨⟨cyl, F, p, hcenter, G, hsource, hQ, cmp⟩⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endChart ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endChart

omit [SigmaCompactSpace W] in
noncomputable def neckTube (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g)
    (ray : EndRay H.endpoint) (d : ℕ → ℝ) (i : ℕ) : GlobalNeckTube W := by
  classical
  exact if h : ray.point (d i) ∈ H.subend (tailIndex g H) then
    (endChart g H (ray.point (d i)) h).cross.tube
  else H.tube

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckTube then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckTube"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckTube ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckTube

omit [SigmaCompactSpace W] in
theorem eventually_mem_tail (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g)
    (ray : EndRay H.endpoint) (d : ℕ → ℝ) (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0)) :
    ∀ᶠ i in Filter.atTop, ray.point (d i) ∈ H.subend (tailIndex g H) := by
  have hdist : Filter.Tendsto
      (fun i => _root_.Dist.dist (ray.point (d i) : UniformSpace.Completion W) H.endpoint) Filter.atTop
      (nhds 0) := by
    simpa only [ray.radial _ (hd _)] using hzero
  exact finiteHorn_eventually_mem_subend g H
    ((tendsto_iff_dist_tendsto_zero).mpr hdist) (tailIndex g H)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_mem_tail then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_mem_tail"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_mem_tail ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_mem_tail

noncomputable def transverseShortcutConstant (W : Type u) [MetricSpace W]
    [ChartedSpace ThreeSpace W] [IsManifold I3 ∞ W] : ℝ :=
  Classical.choose (exists_uniform_transverse_shortcuts (M := W))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.transverseShortcutConstant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.transverseShortcutConstant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.transverseShortcutConstant ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.transverseShortcutConstant

omit [SigmaCompactSpace W] in
theorem transverseShortcutConstant_pos (W : Type u) [MetricSpace W]
    [ChartedSpace ThreeSpace W] [IsManifold I3 ∞ W] :
    0 < transverseShortcutConstant W :=
  (Classical.choose_spec (exists_uniform_transverse_shortcuts (M := W))).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.transverseShortcutConstant_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.transverseShortcutConstant_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.transverseShortcutConstant_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.transverseShortcutConstant_pos

omit [SigmaCompactSpace W] in
theorem transverseShortcutConstant_spec (W : Type u) [MetricSpace W]
    [ChartedSpace ThreeSpace W] [IsManifold I3 ∞ W] :
    ∀ (C : CylinderReference) (h : ℝ → SmoothRiemannianMetric IC Cylinder)
      (g : ℝ → SmoothRiemannianMetric I3 W) (F : PartialDiffeomorph IC I3 Cylinder W ∞)
      (U : Set Cylinder) (times : Set ℝ) (order : ℕ) (eps z : ℝ),
      MetricComparisonOn h g F U times order eps → h 0 = C.metric 0 → 0 ≤ eps → eps ≤ 1 →
      0 ∈ times → U ⊆ F.source → (∀ y : Sphere 2, (y, z) ∈ U) → ∀ x y : Sphere 2,
      ∃ gamma : ℝ → W, gamma 0 = F (x, z) ∧ gamma 1 = F (y, z) ∧
        ContMDiffOn 𝓘(ℝ, ℝ) I3 1 gamma (Set.Icc (0 : ℝ) 1) ∧
        (∀ s ∈ Set.Icc (0 : ℝ) 1, gamma s ∈ F '' (Set.univ ×ˢ ({z} : Set ℝ))) ∧
        metricPathELength (g 0) gamma 0 1 ≤ ENNReal.ofReal (transverseShortcutConstant W) :=
  (Classical.choose_spec (exists_uniform_transverse_shortcuts (M := W))).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.transverseShortcutConstant_spec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.transverseShortcutConstant_spec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.transverseShortcutConstant_spec ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.transverseShortcutConstant_spec

omit [SigmaCompactSpace W] in
theorem endChart_section_diameter_le (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g)
    (x : W) (hx : x ∈ H.subend (tailIndex g H)) :
    ∀ y ∈ (endChart g H x hx).cross.tube.sectionSet (1 / 2),
      dist x y ≤ transverseShortcutConstant W / Real.sqrt (metricScalarAt g x) := by
  set E := endChart g H x hx with hE
  intro y hy
  have hy' : y ∈ Set.range (fun q : Sphere 2 => E.F (q, (0 : ℝ))) := by
    rw [← GlobalNeckTube.range_sectionMap E.cross.tube (1 / 2),
      show (fun q : Sphere 2 => E.cross.tube.map (q, 1 / 2)) =
        (fun q : Sphere 2 => E.F (q, 0)) from funext E.cross.center_eq] at hy
    exact hy
  obtain ⟨q, hq⟩ := hy'
  rw [← hq]
  have hlevel : ∀ z : Sphere 2, (z, (0 : ℝ)) ∈
      (Set.univ ×ˢ Set.Icc (-H.collar_depth) H.collar_depth : Set Cylinder) := by
    intro z
    exact ⟨Set.mem_univ _, by constructor <;> linarith [H.collar_depth_pos]⟩
  obtain ⟨gamma, hstart, hend, hsmooth, _hmem, hlen⟩ :=
    transverseShortcutConstant_spec W E.cyl (fun _ => E.cyl.metric 0)
      (fun _ => scaleMetric (metricScalarAt g x) E.Q_pos g) E.F
      (Set.univ ×ˢ Set.Icc (-H.collar_depth) H.collar_depth) {0}
      (⌈H.neck_precision⁻¹⌉₊) H.neck_precision 0 E.cmp rfl H.neck_precision_pos.le
      (by linarith [H.neck_precision_small]) (by simp) E.source_sub hlevel E.p q
  have hdist := (edistOf_le_metricPathELength
    (scaleMetric (metricScalarAt g x) E.Q_pos g) (by norm_num : (0 : ℝ) ≤ 1) hsmooth).trans hlen
  rw [hstart, hend, E.center, edistOf_scale] at hdist
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hdist
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
    ENNReal.toReal_ofReal (transverseShortcutConstant_pos W).le] at hreal
  change Real.sqrt (metricScalarAt g x) * metricDistance g x (E.F (q, 0)) ≤
    transverseShortcutConstant W at hreal
  rw [← H.intrinsic] at hreal
  exact (le_div_iff₀ (Real.sqrt_pos.mpr E.Q_pos)).mpr (by linarith)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endChart_section_diameter_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endChart_section_diameter_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endChart_section_diameter_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endChart_section_diameter_le

omit [SigmaCompactSpace W] in
theorem EndChart.section_diameter_le {g : SmoothRiemannianMetric I3 W} {H : FiniteHorn g}
    {x : W} {hx : x ∈ H.subend (tailIndex g H)} (E : EndChart g H x hx) :
    ∀ y ∈ E.cross.tube.sectionSet (1 / 2),
      dist x y ≤ transverseShortcutConstant W / Real.sqrt (metricScalarAt g x) := by
  intro y hy
  have hyspan : y ∈ Set.range (fun q : Sphere 2 => E.F (q, (0 : ℝ))) := by
    rw [← GlobalNeckTube.range_sectionMap E.cross.tube (1 / 2)] at hy
    simpa only [E.cross.center_eq] using hy
  obtain ⟨q, hq⟩ := hyspan
  rw [← hq]
  have hcyl : ∀ z : Sphere 2, (z, (0 : ℝ)) ∈
      (Set.univ ×ˢ Set.Icc (-H.collar_depth) H.collar_depth : Set Cylinder) := by
    intro z
    exact ⟨Set.mem_univ _, by constructor <;> linarith [H.collar_depth_pos]⟩
  obtain ⟨gam, hgam0, hgam1, hgsm, _hgm, hglen⟩ :=
    transverseShortcutConstant_spec W E.cyl (fun _ => E.cyl.metric 0)
      (fun _ => scaleMetric (metricScalarAt g x) E.Q_pos g) E.F
      (Set.univ ×ˢ Set.Icc (-H.collar_depth) H.collar_depth) {0}
      (⌈H.neck_precision⁻¹⌉₊) H.neck_precision 0 E.cmp rfl H.neck_precision_pos.le
      (by linarith [H.neck_precision_small]) (by simp) E.source_sub hcyl E.p q
  have hlength' := (edistOf_le_metricPathELength
    (scaleMetric (metricScalarAt g x) E.Q_pos g) (by norm_num : (0 : ℝ) ≤ 1) hgsm).trans hglen
  have hreal : Real.sqrt (metricScalarAt g x) * metricDistance g x (E.F (q, 0)) ≤
      transverseShortcutConstant W := by
    have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlength'
    rw [hgam0, hgam1, E.center, edistOf_scale] at h1
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
      ENNReal.toReal_ofReal (transverseShortcutConstant_pos W).le] at h1
    exact h1
  exact (le_div_iff₀ (Real.sqrt_pos.mpr E.Q_pos)).mpr (by rw [H.intrinsic]; linarith)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndChart
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndChart.section_diameter_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndChart.section_diameter_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndChart.section_diameter_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndChart.section_diameter_le

private theorem sqrt_ratio_bound {L eta s e : ℝ} (hL : 0 < L) (heta : 0 < eta)
    (h : (2 * L / eta) ^ 2 < s * e) :
    L / Real.sqrt (s * e) < eta / 2 := by
  have hpos : 0 < 2 * L / eta := by positivity
  have hlt : 2 * L / eta < Real.sqrt (s * e) := by
    rw [Real.lt_sqrt hpos.le]
    exact h
  have hdiv := div_lt_div_of_pos_left hL hpos hlt
  have heq : L / (2 * L / eta) = eta / 2 := by
    field_simp
  simpa only [heq] using hdiv

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.sqrt_ratio_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.sqrt_ratio_bound target :: scope.openDecls } }

private theorem div_sqrt_lt_mul {L eta s d : ℝ} (hs : 0 < s) (hd : 0 < d)
    (h : L / Real.sqrt (s * d ^ 2) < eta) : L / Real.sqrt s < d * eta := by
  have hsqrt : Real.sqrt (s * d ^ 2) = Real.sqrt s * d := by
    rw [Real.sqrt_mul hs.le, Real.sqrt_sq hd.le]
  rw [hsqrt] at h
  have hne : Real.sqrt s ≠ 0 := by positivity
  calc L / Real.sqrt s = d * (L / (Real.sqrt s * d)) := by
        field_simp
    _ < d * eta := mul_lt_mul_of_pos_left h hd

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.div_sqrt_lt_mul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.div_sqrt_lt_mul target :: scope.openDecls } }

def NeckEndScale (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g) (ray : EndRay H.endpoint)
    (d : ℕ → ℝ) : Prop :=
  ∀ a b : ℝ, -1 < a → -b ≤ a → a < b → b < 1 / 10 → ∀ᶠ i in Filter.atTop, ∃ j : ℕ,
    {x : W | _root_.Dist.dist (x : UniformSpace.Completion W) H.endpoint < (1 - a) * d i} ⊆ H.subend j ∧
    H.subend j ⊆ {x : W | _root_.Dist.dist (x : UniformSpace.Completion W) H.endpoint < (1 + b) * d i} ∧
    (∀ x ∈ H.subend j, (neckTube g H ray d i).height x < 1 / 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.NeckEndScale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.NeckEndScale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.NeckEndScale ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.NeckEndScale

omit [SigmaCompactSpace W] in
theorem neckSectionBarrier_of_neckEndScale (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g)
    (ray : EndRay H.endpoint) (d : ℕ → ℝ) (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop)
    (hscale : NeckEndScale g H ray d) : Nonempty (NeckSectionBarrier H ray d) := by
  classical
  refine ⟨neckTube g H ray d, ?_, ?_⟩
  · refine ⟨transverseShortcutConstant W, transverseShortcutConstant_pos W, ?_⟩
    filter_upwards [eventually_mem_tail g H ray d hd hzero] with i hgood
    have htube : neckTube g H ray d i = (endChart g H (ray.point (d i)) hgood).cross.tube := by
      rw [neckTube, dif_pos hgood]
    intro x hx
    rw [htube] at hx
    exact endChart_section_diameter_le g H (ray.point (d i)) hgood x hx
  · intro eta heta heta10
    have hb0 : eta < (eta + 1 / 10) / 2 := by linarith
    have hb0' : (eta + 1 / 10) / 2 < 1 / 10 := by linarith
    have ha1 : -1 < -(eta / 2) := by linarith
    have hb1 : eta / 2 < 1 / 10 := by linarith
    filter_upwards [eventually_mem_tail g H ray d hd hzero,
      hscale eta ((eta + 1 / 10) / 2) (by linarith) (by linarith) hb0 hb0',
      hscale (-(eta / 2)) (eta / 2) ha1 (by linarith) (by linarith) hb1,
      hlarge.eventually_ge_atTop (_root_.Max.max 1 ((2 * transverseShortcutConstant W / eta) ^ 2 + 1))]
      with i hgood hj0 hj1 hbig
    obtain ⟨j0, hsub0, _hsup0, hdeep0⟩ := hj0
    obtain ⟨j1, hsub1, hsup1, _hdeep1⟩ := hj1
    set E := endChart g H (ray.point (d i)) hgood with hE
    have htube : neckTube g H ray d i = E.cross.tube := by rw [neckTube, dif_pos hgood]
    have hdpos : 0 < d i := (hd i).1
    have hsmul : 1 ≤ metricScalarAt g (ray.point (d i)) * d i ^ 2 :=
      le_trans (le_max_left _ _) hbig
    have hs_pos : 0 < metricScalarAt g (ray.point (d i)) := by
      nlinarith [hsmul, sq_nonneg (d i), sq_pos_of_pos hdpos]
    have hspread : transverseShortcutConstant W /
        Real.sqrt (metricScalarAt g (ray.point (d i)) * d i ^ 2) < eta / 2 := by
      refine sqrt_ratio_bound (transverseShortcutConstant_pos W) heta ?_
      have h2 : (2 * transverseShortcutConstant W / eta) ^ 2 + 1 ≤
          metricScalarAt g (ray.point (d i)) * d i ^ 2 := le_trans (le_max_right _ _) hbig
      linarith
    have hcenter_ball : ∀ q : Sphere 2,
        dist (E.F (q, 0) : UniformSpace.Completion W) H.endpoint < (1 - (-(eta / 2))) * d i := by
      intro q
      have hdiam := endChart_section_diameter_le g H (ray.point (d i)) hgood (E.F (q, 0))
        (by
          rw [← GlobalNeckTube.range_sectionMap E.cross.tube (1 / 2),
            show (fun r : Sphere 2 => E.cross.tube.map (r, 1 / 2)) =
              (fun r : Sphere 2 => E.F (r, 0)) from funext E.cross.center_eq]
          exact ⟨q, rfl⟩)
      have hle : transverseShortcutConstant W /
          Real.sqrt (metricScalarAt g (ray.point (d i))) < d i * (eta / 2) :=
        div_sqrt_lt_mul hs_pos hdpos hspread
      have hlt : _root_.Dist.dist (ray.point (d i)) (E.F (q, 0)) < (eta / 2) * d i := by
        rw [mul_comm (eta / 2) (d i)]
        exact lt_of_le_of_lt hdiam hle
      calc _root_.Dist.dist (E.F (q, 0) : UniformSpace.Completion W) H.endpoint
          ≤ _root_.Dist.dist (E.F (q, 0) : UniformSpace.Completion W)
              (ray.point (d i) : UniformSpace.Completion W) +
            dist (ray.point (d i) : UniformSpace.Completion W) H.endpoint := dist_triangle _ _ _
        _ = _root_.Dist.dist (ray.point (d i)) (E.F (q, 0)) + d i := by
              rw [UniformSpace.Completion.dist_eq, dist_comm (E.F (q, 0)) (ray.point (d i)),
                ray.radial (d i) (hd i)]
        _ < (eta / 2) * d i + d i := by linarith
        _ = (1 - (-(eta / 2))) * d i := by ring
    have hcenter_sub1 : ∀ q : Sphere 2, E.F (q, 0) ∈ H.subend j1 :=
      fun q => hsub1 (hcenter_ball q)
    intro c hc0 hc1
    have hc0' : _root_.Dist.dist (c ⟨0, by simp⟩ : UniformSpace.Completion W) H.endpoint <
        (1 - eta) * d i := by
      rw [div_lt_iff₀ hdpos] at hc0
      linarith
    have hh0 : E.cross.tube.height (c ⟨0, by simp⟩) < 1 / 2 := by
      have h := hdeep0 (c ⟨0, by simp⟩) (hsub0 hc0')
      rwa [htube] at h
    have hout1 : c ⟨1, by simp⟩ ∉ H.subend j1 := by
      intro hmem
      have h := hsup1 hmem
      have hmono : (1 + eta / 2) * d i < (1 + eta) * d i :=
        mul_lt_mul_of_pos_right (by linarith) hdpos
      rw [lt_div_iff₀ hdpos] at hc1
      exact (not_lt_of_ge (hmono.trans hc1).le) h
    have hh1 : 1 / 2 < E.cross.tube.height (c ⟨1, by simp⟩) :=
      GlobalNeckCrossSection.outer_side_of_center_in_subend g H E.cross j1 hcenter_sub1 _
        hout1
    let gamma : ℝ → W := fun t => c (Set.projIcc (0 : ℝ) 1 (by norm_num) t)
    have hcont : ContinuousOn gamma (Set.Icc (0 : ℝ) 1) :=
      (c.continuous.comp continuous_projIcc).continuousOn
    have hg0 : gamma 0 = c ⟨0, by simp⟩ := by
      simp only [gamma, Set.projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1)]
    have hg1 : gamma 1 = c ⟨1, by simp⟩ := by
      simp only [gamma, Set.projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1)]
    obtain ⟨s, hs, hmem⟩ := E.cross.path_meets_center gamma hcont (by rw [hg0]; exact hh0)
      (by rw [hg1]; exact hh1)
    refine ⟨⟨s, hs⟩, ?_⟩
    have hmem' : c ⟨s, hs⟩ ∈ Set.range (fun q : Sphere 2 => E.F (q, (0 : ℝ))) := by
      rwa [show gamma s = c ⟨s, hs⟩ from by
        simp only [gamma, Set.projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1) hs]] at hmem
    rw [htube, ← GlobalNeckTube.range_sectionMap E.cross.tube (1 / 2),
      show (fun q : Sphere 2 => E.cross.tube.map (q, 1 / 2)) =
        (fun q : Sphere 2 => E.F (q, 0)) from funext E.cross.center_eq]
    exact hmem'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckSectionBarrier_of_neckEndScale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckSectionBarrier_of_neckEndScale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckSectionBarrier_of_neckEndScale ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckSectionBarrier_of_neckEndScale

omit [SigmaCompactSpace W] in
theorem nonempty_hornBarriers_of_neckEndScale (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g)
    (ray : EndRay H.endpoint) (d : ℕ → ℝ) (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop)
    (hscale : NeckEndScale g H ray d) : Nonempty (HornBarriers H ray d) := by
  obtain ⟨b⟩ := neckSectionBarrier_of_neckEndScale g H ray d hd hzero hlarge hscale
  exact nonempty_hornBarriers_of_neckSectionBarrier H ray d b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_hornBarriers_of_neckEndScale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_hornBarriers_of_neckEndScale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_hornBarriers_of_neckEndScale ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_hornBarriers_of_neckEndScale

def NeckEndScaleWindow (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g)
    (ray : EndRay H.endpoint) (d : ℕ → ℝ) : Prop :=
  (∀ e : ℝ, 0 < e → e < 1 / 10 → ∀ᶠ i in Filter.atTop, ∃ j : ℕ,
    {x : W | _root_.Dist.dist (x : UniformSpace.Completion W) H.endpoint < (1 - e) * d i} ⊆ H.subend j ∧
    (∀ x ∈ H.subend j, (neckTube g H ray d i).height x < 1 / 2)) ∧
  (∀ e : ℝ, 0 < e → e < 1 / 10 → ∀ᶠ i in Filter.atTop, ∃ j : ℕ,
    {x : W | _root_.Dist.dist (x : UniformSpace.Completion W) H.endpoint < (1 + e / 2) * d i} ⊆ H.subend j ∧
    H.subend j ⊆ {x : W | _root_.Dist.dist (x : UniformSpace.Completion W) H.endpoint < (1 + e) * d i})

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.NeckEndScaleWindow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.NeckEndScaleWindow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.NeckEndScaleWindow ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.NeckEndScaleWindow

omit [SigmaCompactSpace W] in
theorem neckEndScaleWindow_of_neckEndScale (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g)
    (ray : EndRay H.endpoint) (d : ℕ → ℝ) (hscale : NeckEndScale g H ray d) :
    NeckEndScaleWindow g H ray d := by
  constructor
  · intro e he he10
    filter_upwards [hscale e ((e + 1 / 10) / 2) (by linarith) (by linarith) (by linarith)
      (by linarith)]
      with i hi
    obtain ⟨j, hsub, _hsup, hdeep⟩ := hi
    exact ⟨j, hsub, hdeep⟩
  · intro e he he10
    filter_upwards [hscale (-(e / 2)) e (by linarith) (by linarith) (by linarith)
      (by linarith)] with i hi
    obtain ⟨j, hsub, hsup, _hdeep⟩ := hi
    have hrad : 1 - -(e / 2) = 1 + e / 2 := by ring
    rw [hrad] at hsub
    exact ⟨j, hsub, hsup⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckEndScaleWindow_of_neckEndScale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckEndScaleWindow_of_neckEndScale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckEndScaleWindow_of_neckEndScale ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckEndScaleWindow_of_neckEndScale

omit [SigmaCompactSpace W] in
theorem neckEndScale_subend_eq_ball (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g)
    (ray : EndRay H.endpoint) (d : ℕ → ℝ) (hscale : NeckEndScale g H ray d)
    {eta : ℝ} (heta : 0 < eta) (heta10 : eta < 1 / 10) :
    ∀ᶠ i in Filter.atTop, ∃ j : ℕ, H.subend j =
      {x : W | _root_.Dist.dist (x : UniformSpace.Completion W) H.endpoint < (1 + eta / 2) * d i} := by
  filter_upwards [hscale (-(eta / 2)) (eta / 2) (by linarith) (by linarith) (by linarith)
    (by linarith)]
    with i hi
  obtain ⟨j, hsub, hsup, _hdeep⟩ := hi
  have hrad : 1 - -(eta / 2) = 1 + eta / 2 := by ring
  rw [hrad] at hsub
  exact ⟨j, Set.Subset.antisymm hsup hsub⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckEndScale_subend_eq_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckEndScale_subend_eq_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckEndScale_subend_eq_ball ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckEndScale_subend_eq_ball

omit [SigmaCompactSpace W] in
theorem neckSectionBarrier_of_neckEndScaleWindow (g : SmoothRiemannianMetric I3 W)
    (H : FiniteHorn g) (ray : EndRay H.endpoint) (d : ℕ → ℝ)
    (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop)
    (hscale : NeckEndScaleWindow g H ray d) : Nonempty (NeckSectionBarrier H ray d) := by
  classical
  refine ⟨neckTube g H ray d, ?_, ?_⟩
  · refine ⟨transverseShortcutConstant W, transverseShortcutConstant_pos W, ?_⟩
    filter_upwards [eventually_mem_tail g H ray d hd hzero] with i hgood
    have htube : neckTube g H ray d i = (endChart g H (ray.point (d i)) hgood).cross.tube := by
      rw [neckTube, dif_pos hgood]
    intro x hx
    rw [htube] at hx
    exact endChart_section_diameter_le g H (ray.point (d i)) hgood x hx
  · intro eta heta heta10
    filter_upwards [eventually_mem_tail g H ray d hd hzero,
      hscale.1 eta heta heta10,
      hscale.2 eta heta heta10,
      hlarge.eventually_ge_atTop (_root_.Max.max 1 ((2 * transverseShortcutConstant W / eta) ^ 2 + 1))]
      with i hgood hj0 hj1 hbig
    obtain ⟨j0, hsub0, hdeep0⟩ := hj0
    obtain ⟨j1, hsub1, hsup1⟩ := hj1
    set E := endChart g H (ray.point (d i)) hgood with hE
    have htube : neckTube g H ray d i = E.cross.tube := by rw [neckTube, dif_pos hgood]
    have hdpos : 0 < d i := (hd i).1
    have hsmul : 1 ≤ metricScalarAt g (ray.point (d i)) * d i ^ 2 :=
      le_trans (le_max_left _ _) hbig
    have hs_pos : 0 < metricScalarAt g (ray.point (d i)) := by
      nlinarith [hsmul, sq_nonneg (d i), sq_pos_of_pos hdpos]
    have hspread : transverseShortcutConstant W /
        Real.sqrt (metricScalarAt g (ray.point (d i)) * d i ^ 2) < eta / 2 := by
      refine sqrt_ratio_bound (transverseShortcutConstant_pos W) heta ?_
      have h2 : (2 * transverseShortcutConstant W / eta) ^ 2 + 1 ≤
          metricScalarAt g (ray.point (d i)) * d i ^ 2 := le_trans (le_max_right _ _) hbig
      linarith
    have hcenter_ball : ∀ q : Sphere 2,
        dist (E.F (q, 0) : UniformSpace.Completion W) H.endpoint < (1 + eta / 2) * d i := by
      intro q
      have hrad : (1 - (-(eta / 2))) * d i = (1 + eta / 2) * d i := by ring
      rw [← hrad]
      have hdiam := endChart_section_diameter_le g H (ray.point (d i)) hgood (E.F (q, 0))
        (by
          rw [← GlobalNeckTube.range_sectionMap E.cross.tube (1 / 2),
            show (fun r : Sphere 2 => E.cross.tube.map (r, 1 / 2)) =
              (fun r : Sphere 2 => E.F (r, 0)) from funext E.cross.center_eq]
          exact ⟨q, rfl⟩)
      have hle : transverseShortcutConstant W /
          Real.sqrt (metricScalarAt g (ray.point (d i))) < d i * (eta / 2) :=
        div_sqrt_lt_mul hs_pos hdpos hspread
      have hlt : _root_.Dist.dist (ray.point (d i)) (E.F (q, 0)) < (eta / 2) * d i := by
        rw [mul_comm (eta / 2) (d i)]
        exact lt_of_le_of_lt hdiam hle
      calc _root_.Dist.dist (E.F (q, 0) : UniformSpace.Completion W) H.endpoint
          ≤ _root_.Dist.dist (E.F (q, 0) : UniformSpace.Completion W)
              (ray.point (d i) : UniformSpace.Completion W) +
            dist (ray.point (d i) : UniformSpace.Completion W) H.endpoint := dist_triangle _ _ _
        _ = _root_.Dist.dist (ray.point (d i)) (E.F (q, 0)) + d i := by
              rw [UniformSpace.Completion.dist_eq, dist_comm (E.F (q, 0)) (ray.point (d i)),
                ray.radial (d i) (hd i)]
        _ < (eta / 2) * d i + d i := by linarith
        _ = (1 - (-(eta / 2))) * d i := by ring
    have hcenter_sub1 : ∀ q : Sphere 2, E.F (q, 0) ∈ H.subend j1 :=
      fun q => hsub1 (hcenter_ball q)
    intro c hc0 hc1
    have hc0' : _root_.Dist.dist (c ⟨0, by simp⟩ : UniformSpace.Completion W) H.endpoint <
        (1 - eta) * d i := by
      rw [div_lt_iff₀ hdpos] at hc0
      linarith
    have hh0 : E.cross.tube.height (c ⟨0, by simp⟩) < 1 / 2 := by
      have h := hdeep0 (c ⟨0, by simp⟩) (hsub0 hc0')
      rwa [htube] at h
    have hout1 : c ⟨1, by simp⟩ ∉ H.subend j1 := by
      intro hmem
      have h := hsup1 hmem
      rw [lt_div_iff₀ hdpos] at hc1
      exact (not_lt_of_ge hc1.le) h
    have hh1 : 1 / 2 < E.cross.tube.height (c ⟨1, by simp⟩) :=
      GlobalNeckCrossSection.outer_side_of_center_in_subend g H E.cross j1 hcenter_sub1 _
        hout1
    let gamma : ℝ → W := fun t => c (Set.projIcc (0 : ℝ) 1 (by norm_num) t)
    have hcont : ContinuousOn gamma (Set.Icc (0 : ℝ) 1) :=
      (c.continuous.comp continuous_projIcc).continuousOn
    have hg0 : gamma 0 = c ⟨0, by simp⟩ := by
      simp only [gamma, Set.projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1)
        (by norm_num : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1)]
    have hg1 : gamma 1 = c ⟨1, by simp⟩ := by
      simp only [gamma, Set.projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1)
        (by norm_num : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1)]
    obtain ⟨s, hs, hmem⟩ := E.cross.path_meets_center gamma hcont (by rw [hg0]; exact hh0)
      (by rw [hg1]; exact hh1)
    refine ⟨⟨s, hs⟩, ?_⟩
    have hmem' : c ⟨s, hs⟩ ∈ Set.range (fun q : Sphere 2 => E.F (q, (0 : ℝ))) := by
      rwa [show gamma s = c ⟨s, hs⟩ from by
        simp only [gamma, Set.projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1) hs]] at hmem
    rw [htube, ← GlobalNeckTube.range_sectionMap E.cross.tube (1 / 2),
      show (fun q : Sphere 2 => E.cross.tube.map (q, 1 / 2)) =
        (fun q : Sphere 2 => E.F (q, 0)) from funext E.cross.center_eq]
    exact hmem'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckSectionBarrier_of_neckEndScaleWindow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckSectionBarrier_of_neckEndScaleWindow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckSectionBarrier_of_neckEndScaleWindow ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckSectionBarrier_of_neckEndScaleWindow

omit [SigmaCompactSpace W] in
theorem nonempty_hornBarriers_of_neckEndScaleWindow (g : SmoothRiemannianMetric I3 W)
    (H : FiniteHorn g) (ray : EndRay H.endpoint) (d : ℕ → ℝ)
    (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop)
    (hscale : NeckEndScaleWindow g H ray d) : Nonempty (HornBarriers H ray d) := by
  obtain ⟨b⟩ := neckSectionBarrier_of_neckEndScaleWindow g H ray d hd hzero hlarge hscale
  exact nonempty_hornBarriers_of_neckSectionBarrier H ray d b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_hornBarriers_of_neckEndScaleWindow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_hornBarriers_of_neckEndScaleWindow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_hornBarriers_of_neckEndScaleWindow ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_hornBarriers_of_neckEndScaleWindow

def HornRadialPosition (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g)
    (ray : EndRay H.endpoint) (d : ℕ → ℝ) : Prop :=
  ∀ e : ℝ, 0 < e → e < 1 / 10 → ∀ᶠ i in Filter.atTop,
    (∀ x : W, _root_.Dist.dist (x : UniformSpace.Completion W) H.endpoint < (1 - e) * d i →
      (neckTube g H ray d i).height x < 1 / 2) ∧
    (∀ x : W, (1 + e) * d i < _root_.Dist.dist (x : UniformSpace.Completion W) H.endpoint →
      (1 / 2 : ℝ) < (neckTube g H ray d i).height x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.HornRadialPosition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.HornRadialPosition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.HornRadialPosition ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.HornRadialPosition

omit [SigmaCompactSpace W] in
theorem neckSectionBarrier_of_hornRadialPosition (g : SmoothRiemannianMetric I3 W)
    (H : FiniteHorn g) (ray : EndRay H.endpoint) (d : ℕ → ℝ)
    (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hpos : HornRadialPosition g H ray d) : Nonempty (NeckSectionBarrier H ray d) := by
  classical
  refine ⟨neckTube g H ray d, ?_, ?_⟩
  · refine ⟨transverseShortcutConstant W, transverseShortcutConstant_pos W, ?_⟩
    filter_upwards [eventually_mem_tail g H ray d hd hzero] with i hgood
    have htube : neckTube g H ray d i = (endChart g H (ray.point (d i)) hgood).cross.tube := by
      rw [neckTube, dif_pos hgood]
    intro x hx
    rw [htube] at hx
    exact endChart_section_diameter_le g H (ray.point (d i)) hgood x hx
  · intro eta heta heta10
    filter_upwards [hpos eta heta heta10, eventually_mem_tail g H ray d hd hzero]
      with i hR hgood
    obtain ⟨htip, houter⟩ := hR
    set E := endChart g H (ray.point (d i)) hgood with hE
    have htube : neckTube g H ray d i = E.cross.tube := by rw [neckTube, dif_pos hgood]
    have hdpos : 0 < d i := (hd i).1
    intro c hc0 hc1
    have hc0' : _root_.Dist.dist (c ⟨0, by simp⟩ : UniformSpace.Completion W) H.endpoint <
        (1 - eta) * d i := by
      rw [div_lt_iff₀ hdpos] at hc0
      linarith
    have hstart : E.cross.tube.height (c ⟨0, by simp⟩) < 1 / 2 := by
      have h := htip (c ⟨0, by simp⟩) hc0'
      rwa [htube] at h
    have hc1' : (1 + eta) * d i <
        dist (c ⟨1, by simp⟩ : UniformSpace.Completion W) H.endpoint := by
      rw [lt_div_iff₀ hdpos] at hc1
      linarith
    have hend : 1 / 2 < E.cross.tube.height (c ⟨1, by simp⟩) := by
      have h := houter (c ⟨1, by simp⟩) hc1'
      rwa [htube] at h
    let gamma : ℝ → W := fun t => c (Set.projIcc (0 : ℝ) 1 (by norm_num) t)
    have hcont : ContinuousOn gamma (Set.Icc (0 : ℝ) 1) :=
      (c.continuous.comp continuous_projIcc).continuousOn
    have hg0 : gamma 0 = c ⟨0, by simp⟩ := by
      simp only [gamma, Set.projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1)
        (by norm_num : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1)]
    have hg1 : gamma 1 = c ⟨1, by simp⟩ := by
      simp only [gamma, Set.projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1)
        (by norm_num : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1)]
    obtain ⟨s, hs, hmem⟩ := E.cross.path_meets_center gamma hcont (by rw [hg0]; exact hstart)
      (by rw [hg1]; exact hend)
    refine ⟨⟨s, hs⟩, ?_⟩
    have hmem' : c ⟨s, hs⟩ ∈ Set.range (fun q : Sphere 2 => E.F (q, (0 : ℝ))) := by
      rwa [show gamma s = c ⟨s, hs⟩ from by
        simp only [gamma, Set.projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1) hs]] at hmem
    rw [htube, ← GlobalNeckTube.range_sectionMap E.cross.tube (1 / 2),
      show (fun q : Sphere 2 => E.cross.tube.map (q, 1 / 2)) =
        (fun q : Sphere 2 => E.F (q, 0)) from funext E.cross.center_eq]
    exact hmem'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckSectionBarrier_of_hornRadialPosition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckSectionBarrier_of_hornRadialPosition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckSectionBarrier_of_hornRadialPosition ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckSectionBarrier_of_hornRadialPosition

omit [SigmaCompactSpace W] in
theorem hornRadialPosition_of_neckEndScaleWindow (g : SmoothRiemannianMetric I3 W)
    (H : FiniteHorn g) (ray : EndRay H.endpoint) (d : ℕ → ℝ)
    (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop)
    (hscale : NeckEndScaleWindow g H ray d) : HornRadialPosition g H ray d := by
  intro e he he10
  filter_upwards [hscale.1 e he he10, hscale.2 e he he10,
    eventually_mem_tail g H ray d hd hzero,
    hlarge.eventually_ge_atTop (_root_.Max.max 1 ((2 * transverseShortcutConstant W / e) ^ 2 + 1))]
    with i htip hj1 hgood hbig
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨j0, hsub0, hdeep0⟩ := htip
    exact hdeep0 x (hsub0 hx)
  · intro x hx
    obtain ⟨j1, hsub1, hsup1⟩ := hj1
    set E := endChart g H (ray.point (d i)) hgood with hE
    have htube : neckTube g H ray d i = E.cross.tube := by rw [neckTube, dif_pos hgood]
    have hdpos : 0 < d i := (hd i).1
    have hsmul : 1 ≤ metricScalarAt g (ray.point (d i)) * d i ^ 2 :=
      le_trans (le_max_left _ _) hbig
    have hs_pos : 0 < metricScalarAt g (ray.point (d i)) := by
      nlinarith [hsmul, sq_nonneg (d i), sq_pos_of_pos hdpos]
    have hspread : transverseShortcutConstant W /
        Real.sqrt (metricScalarAt g (ray.point (d i)) * d i ^ 2) < e / 2 := by
      refine sqrt_ratio_bound (transverseShortcutConstant_pos W) he ?_
      have h2 : (2 * transverseShortcutConstant W / e) ^ 2 + 1 ≤
          metricScalarAt g (ray.point (d i)) * d i ^ 2 := le_trans (le_max_right _ _) hbig
      linarith
    have hcenter_ball : ∀ q : Sphere 2,
        dist (E.F (q, 0) : UniformSpace.Completion W) H.endpoint < (1 + e / 2) * d i := by
      intro q
      have hrad : (1 - (-(e / 2))) * d i = (1 + e / 2) * d i := by ring
      rw [← hrad]
      have hdiam := endChart_section_diameter_le g H (ray.point (d i)) hgood (E.F (q, 0))
        (by
          rw [← GlobalNeckTube.range_sectionMap E.cross.tube (1 / 2),
            show (fun r : Sphere 2 => E.cross.tube.map (r, 1 / 2)) =
              (fun r : Sphere 2 => E.F (r, 0)) from funext E.cross.center_eq]
          exact ⟨q, rfl⟩)
      have hle : transverseShortcutConstant W /
          Real.sqrt (metricScalarAt g (ray.point (d i))) < d i * (e / 2) :=
        div_sqrt_lt_mul hs_pos hdpos hspread
      have hlt : _root_.Dist.dist (ray.point (d i)) (E.F (q, 0)) < (e / 2) * d i := by
        rw [mul_comm (e / 2) (d i)]
        exact lt_of_le_of_lt hdiam hle
      calc _root_.Dist.dist (E.F (q, 0) : UniformSpace.Completion W) H.endpoint
          ≤ _root_.Dist.dist (E.F (q, 0) : UniformSpace.Completion W)
              (ray.point (d i) : UniformSpace.Completion W) +
            dist (ray.point (d i) : UniformSpace.Completion W) H.endpoint := dist_triangle _ _ _
        _ = _root_.Dist.dist (ray.point (d i)) (E.F (q, 0)) + d i := by
              rw [UniformSpace.Completion.dist_eq, dist_comm (E.F (q, 0)) (ray.point (d i)),
                ray.radial (d i) (hd i)]
        _ < (e / 2) * d i + d i := by linarith
        _ = (1 - (-(e / 2))) * d i := by ring
    have hcenter_sub1 : ∀ q : Sphere 2, E.F (q, 0) ∈ H.subend j1 :=
      fun q => hsub1 (hcenter_ball q)
    have hout : x ∉ H.subend j1 := by
      intro hmem
      have h := hsup1 hmem
      have h' : _root_.Dist.dist (x : UniformSpace.Completion W) H.endpoint < (1 + e) * d i := h
      linarith
    have h := GlobalNeckCrossSection.outer_side_of_center_in_subend g H E.cross j1 hcenter_sub1 x
      hout
    rwa [htube]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornRadialPosition_of_neckEndScaleWindow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornRadialPosition_of_neckEndScaleWindow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornRadialPosition_of_neckEndScaleWindow ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornRadialPosition_of_neckEndScaleWindow

omit [SigmaCompactSpace W] in
theorem nonempty_hornBarriers_of_hornRadialPosition (g : SmoothRiemannianMetric I3 W)
    (H : FiniteHorn g) (ray : EndRay H.endpoint) (d : ℕ → ℝ)
    (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hpos : HornRadialPosition g H ray d) : Nonempty (HornBarriers H ray d) := by
  obtain ⟨b⟩ := neckSectionBarrier_of_hornRadialPosition g H ray d hd hzero hpos
  exact nonempty_hornBarriers_of_neckSectionBarrier H ray d b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_hornBarriers_of_hornRadialPosition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_hornBarriers_of_hornRadialPosition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_hornBarriers_of_hornRadialPosition ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.nonempty_hornBarriers_of_hornRadialPosition

omit [SigmaCompactSpace W] in
theorem finite_horn_barriers_of_hornRadialPosition {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (_endData : EndGeometry H) (ray : EndRay H.endpoint)
    (d : ℕ → ℝ) (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hpos : HornRadialPosition g H ray d) : Nonempty (HornBarriers H ray d) :=
  nonempty_hornBarriers_of_hornRadialPosition g H ray d hd hzero hpos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_barriers_of_hornRadialPosition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_barriers_of_hornRadialPosition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_barriers_of_hornRadialPosition ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_barriers_of_hornRadialPosition

theorem endChart_height_lt_half_of_dist_lt {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g)
    (ray : EndRay H.endpoint) (d : ℕ → ℝ)
    (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop) :
    ∀ e : ℝ, 0 < e → e < 1 / 10 → ∀ᶠ i in Filter.atTop,
      ∀ (hx : ray.point (d i) ∈ H.subend (tailIndex g H))
        (E : EndChart g H (ray.point (d i)) hx), ∀ x : W,
        _root_.Dist.dist (x : UniformSpace.Completion W) H.endpoint < (1 - e) * d i →
          E.cross.tube.height x < 1 / 2 := by
  classical
  obtain ⟨endData⟩ := finite_horn_end_rays H
  obtain ⟨raysIndex, hrays⟩ := endData.rays
  obtain ⟨deepRadius, hdeepRadius, hdeepBall⟩ := finiteHorn_ball_subset_subend g H raysIndex
  intro e he he10
  have hlim : Filter.Tendsto (fun i => (1 - e) * d i) Filter.atTop (nhds 0) := by
    simpa using hzero.const_mul (1 - e)
  filter_upwards [hlarge.eventually_ge_atTop
      (_root_.Max.max 1 ((2 * transverseShortcutConstant W / e) ^ 2 + 1)),
    hlim.eventually (eventually_lt_nhds hdeepRadius)] with i hbig hdi
  intro hx E x hxlt
  set x₀ : W := ray.point (d i) with hx₀
  have hdpos : 0 < d i := (hd i).1
  have hxend : _root_.Dist.dist (x₀ : UniformSpace.Completion W) H.endpoint = d i := ray.radial (d i) (hd i)
  have hsmul : 1 ≤ metricScalarAt g x₀ * d i ^ 2 := le_trans (le_max_left _ _) hbig
  have hspos : 0 < metricScalarAt g x₀ := by
    nlinarith [hsmul, sq_nonneg (d i), sq_pos_of_pos hdpos]
  have hspread : transverseShortcutConstant W /
      Real.sqrt (metricScalarAt g x₀ * d i ^ 2) < e / 2 := by
    refine sqrt_ratio_bound (transverseShortcutConstant_pos W) he ?_
    have h2 : (2 * transverseShortcutConstant W / e) ^ 2 + 1 ≤
        metricScalarAt g x₀ * d i ^ 2 := le_trans (le_max_right _ _) hbig
    linarith
  have hdiam : transverseShortcutConstant W / Real.sqrt (metricScalarAt g x₀) <
      d i * (e / 2) := div_sqrt_lt_mul hspos hdpos hspread
  have hsec := EndChart.section_diameter_le (g := g) (H := H) (x := x₀) (hx := hx) E
  have hfar : ∀ y ∈ E.cross.tube.sectionSet (1 / 2),
      (1 - e) * d i < _root_.Dist.dist (y : UniformSpace.Completion W) H.endpoint := by
    intro y hy
    have hyb := hsec y hy
    have habs : d i - _root_.Dist.dist x₀ y ≤ _root_.Dist.dist (y : UniformSpace.Completion W) H.endpoint := by
      have h := (abs_le.mp (abs_dist_sub_le (x₀ : UniformSpace.Completion W)
        (y : UniformSpace.Completion W) H.endpoint)).2
      rw [UniformSpace.Completion.dist_eq, hxend] at h
      linarith
    have hlt : (1 - e / 2) * d i < _root_.Dist.dist (y : UniformSpace.Completion W) H.endpoint := by
      nlinarith [habs, hyb, hdiam]
    nlinarith [hlt, he, hdpos]
  have hle : E.cross.tube.height x ≤ 1 / 2 := by
    by_contra hnot
    have hgt : (1 / 2 : ℝ) < E.cross.tube.height x := lt_of_not_ge hnot
    have hdeep : x ∈ H.subend raysIndex := hdeepBall x (by linarith [hxlt, hdi])
    obtain ⟨a, ha⟩ := hrays x hdeep
    obtain ⟨s, hs, p, hp⟩ :=
      GlobalNeckCrossSection.endRay_meets_center g H E.cross a (by rw [ha]; exact hgt)
    have hmem : a.point s ∈ E.cross.tube.sectionSet (1 / 2) := by
      refine ⟨(p, (1 / 2 : ℝ)), ⟨Set.mem_univ _, rfl⟩, ?_⟩
      rw [E.cross.center_eq, hp]
    have hout := hfar (a.point s) hmem
    have hlen : a.length = _root_.Dist.dist (x : UniformSpace.Completion W) H.endpoint := by
      rw [← ha]
      exact (a.radial a.length ⟨a.length_pos, le_rfl⟩).symm
    have hsin : _root_.Dist.dist (a.point s : UniformSpace.Completion W) H.endpoint = s := a.radial s hs
    rw [hsin] at hout
    rw [hlen] at hs
    linarith [hout, hs.2, hxlt]
  have hne : E.cross.tube.height x ≠ 1 / 2 := by
    intro heq
    have hmem : x ∈ E.cross.tube.sectionSet (1 / 2) :=
      (GlobalNeckTube.mem_sectionSet_iff E.cross.tube (by norm_num) x).mpr heq
    have hout := hfar x hmem
    linarith [hout, hxlt]
  exact lt_of_le_of_ne hle hne

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endChart_height_lt_half_of_dist_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endChart_height_lt_half_of_dist_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endChart_height_lt_half_of_dist_lt ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endChart_height_lt_half_of_dist_lt

def HornRadialExitPosition (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g)
    (ray : EndRay H.endpoint) (d : ℕ → ℝ) : Prop :=
  ∀ e : ℝ, 0 < e → e < 1 / 10 → ∀ᶠ i in Filter.atTop,
    ∀ (hx : ray.point (d i) ∈ H.subend (tailIndex g H))
      (E : EndChart g H (ray.point (d i)) hx), ∀ x : W,
      (1 + e) * d i < _root_.Dist.dist (x : UniformSpace.Completion W) H.endpoint →
        (1 / 2 : ℝ) < E.cross.tube.height x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.HornRadialExitPosition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.HornRadialExitPosition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.HornRadialExitPosition ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.HornRadialExitPosition

theorem hornRadialPosition_of_hornRadialExitPosition (g : SmoothRiemannianMetric I3 W)
    (H : FiniteHorn g) (ray : EndRay H.endpoint) (d : ℕ → ℝ)
    (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop)
    (hexit : HornRadialExitPosition g H ray d) : HornRadialPosition g H ray d := by
  intro e he he10
  filter_upwards [endChart_height_lt_half_of_dist_lt H ray d hd hzero hlarge e he he10,
    hexit e he he10, eventually_mem_tail g H ray d hd hzero]
    with i htip hex hgood
  have htube : neckTube g H ray d i =
      (endChart g H (ray.point (d i)) hgood).cross.tube := by
    rw [neckTube, dif_pos hgood]
  refine ⟨?_, ?_⟩ <;> intro x hx
  · rw [htube]
    exact htip hgood (endChart g H (ray.point (d i)) hgood) x hx
  · rw [htube]
    exact hex hgood (endChart g H (ray.point (d i)) hgood) x hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornRadialPosition_of_hornRadialExitPosition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornRadialPosition_of_hornRadialExitPosition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornRadialPosition_of_hornRadialExitPosition ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornRadialPosition_of_hornRadialExitPosition

theorem finite_horn_barriers_of_hornRadialExitPosition {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (endData : EndGeometry H) (ray : EndRay H.endpoint)
    (d : ℕ → ℝ) (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop)
    (hexit : HornRadialExitPosition g H ray d) : Nonempty (HornBarriers H ray d) :=
  finite_horn_barriers_of_hornRadialPosition H endData ray d hd hzero
    (hornRadialPosition_of_hornRadialExitPosition g H ray d hd hzero hlarge hexit)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_barriers_of_hornRadialExitPosition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_barriers_of_hornRadialExitPosition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_barriers_of_hornRadialExitPosition ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_barriers_of_hornRadialExitPosition

def HornRadialExitPositionAtEndChart (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g)
    (ray : EndRay H.endpoint) (d : ℕ → ℝ) : Prop :=
  ∀ e : ℝ, 0 < e → e < 1 / 10 → ∀ᶠ i in Filter.atTop,
    ∀ (hx : ray.point (d i) ∈ H.subend (tailIndex g H)), ∀ x : W,
      (1 + e) * d i < _root_.Dist.dist (x : UniformSpace.Completion W) H.endpoint →
        (1 / 2 : ℝ) < (endChart g H (ray.point (d i)) hx).cross.tube.height x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.HornRadialExitPositionAtEndChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.HornRadialExitPositionAtEndChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.HornRadialExitPositionAtEndChart ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.HornRadialExitPositionAtEndChart

omit [SigmaCompactSpace W] in
theorem hornRadialExitPositionAtEndChart_of_hornRadialExitPosition
    (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g) (ray : EndRay H.endpoint)
    (d : ℕ → ℝ) (hexit : HornRadialExitPosition g H ray d) :
    HornRadialExitPositionAtEndChart g H ray d := by
  intro e he he10
  filter_upwards [hexit e he he10] with i hi hx x hxlt
  exact hi hx (endChart g H (ray.point (d i)) hx) x hxlt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornRadialExitPositionAtEndChart_of_hornRadialExitPosition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornRadialExitPositionAtEndChart_of_hornRadialExitPosition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornRadialExitPositionAtEndChart_of_hornRadialExitPosition ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornRadialExitPositionAtEndChart_of_hornRadialExitPosition

omit [SigmaCompactSpace W] in
theorem hornRadialExitPositionAtEndChart_iff_tipSide_closedBall
    (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g) (ray : EndRay H.endpoint)
    (d : ℕ → ℝ) :
    HornRadialExitPositionAtEndChart g H ray d ↔
      ∀ e : ℝ, 0 < e → e < 1 / 10 → ∀ᶠ i in Filter.atTop,
        ∀ (hx : ray.point (d i) ∈ H.subend (tailIndex g H)), ∀ x : W,
          (endChart g H (ray.point (d i)) hx).cross.tube.height x ≤ 1 / 2 →
            dist (x : UniformSpace.Completion W) H.endpoint ≤ (1 + e) * d i := by
  constructor <;> intro h e he he10
  · filter_upwards [h e he he10] with i hi hx x hxle
    by_contra hcon
    exact (not_lt.mpr hxle) (hi hx x (not_le.mp hcon))
  · filter_upwards [h e he he10] with i hi hx x hxgt
    by_contra hcon
    exact (not_le.mpr hxgt) (hi hx x (not_lt.mp hcon))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornRadialExitPositionAtEndChart_iff_tipSide_closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornRadialExitPositionAtEndChart_iff_tipSide_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornRadialExitPositionAtEndChart_iff_tipSide_closedBall ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornRadialExitPositionAtEndChart_iff_tipSide_closedBall

theorem hornRadialPosition_of_hornRadialExitPositionAtEndChart
    (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g) (ray : EndRay H.endpoint)
    (d : ℕ → ℝ) (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop)
    (hexit : HornRadialExitPositionAtEndChart g H ray d) : HornRadialPosition g H ray d := by
  intro e he he10
  filter_upwards [endChart_height_lt_half_of_dist_lt H ray d hd hzero hlarge e he he10,
    hexit e he he10, eventually_mem_tail g H ray d hd hzero] with i htip hex hgood
  have htube : neckTube g H ray d i =
      (endChart g H (ray.point (d i)) hgood).cross.tube := by
    rw [neckTube, dif_pos hgood]
  refine ⟨?_, ?_⟩ <;> intro x hx
  · rw [htube]
    exact htip hgood (endChart g H (ray.point (d i)) hgood) x hx
  · rw [htube]
    exact hex hgood x hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornRadialPosition_of_hornRadialExitPositionAtEndChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornRadialPosition_of_hornRadialExitPositionAtEndChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornRadialPosition_of_hornRadialExitPositionAtEndChart ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornRadialPosition_of_hornRadialExitPositionAtEndChart

theorem finite_horn_barriers_of_hornRadialExitPositionAtEndChart
    {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g) (endData : EndGeometry H)
    (ray : EndRay H.endpoint) (d : ℕ → ℝ) (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop)
    (hexit : HornRadialExitPositionAtEndChart g H ray d) : Nonempty (HornBarriers H ray d) :=
  finite_horn_barriers_of_hornRadialPosition H endData ray d hd hzero
    (hornRadialPosition_of_hornRadialExitPositionAtEndChart g H ray d hd hzero hlarge hexit)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_barriers_of_hornRadialExitPositionAtEndChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_barriers_of_hornRadialExitPositionAtEndChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_barriers_of_hornRadialExitPositionAtEndChart ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_barriers_of_hornRadialExitPositionAtEndChart

section

open _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set _root_.Submission.DifferentialGeometry.Toponogov

omit [SigmaCompactSpace W] in
theorem eventually_endChart_tip_side_subset_subend {g : SmoothRiemannianMetric I3 W}
    {ι : Type*} {l : Filter ι} (H : FiniteHorn g) (w : ι → W)
    (hw : Filter.Tendsto (fun i => (w i : UniformSpace.Completion W))
      l (nhds H.endpoint)) (j : ℕ) :
    ∀ᶠ i in l,
      ∀ (hx : w i ∈ H.subend (tailIndex g H))
        (E : EndChart g H (w i) hx),
        {x : W | E.cross.tube.height x ≤ 1 / 2} ⊆ H.subend j := by
  obtain ⟨delta, hdelta, hball⟩ := finiteHorn_ball_subset_subend g H j
  obtain ⟨k, hk⟩ := H.curvature_diverges
    ((2 * transverseShortcutConstant W / delta) ^ 2 + 1)
  obtain ⟨deltaK, hdeltaK, hballK⟩ := finiteHorn_ball_subset_subend g H k
  filter_upwards [hw.eventually (Metric.ball_mem_nhds H.endpoint hdeltaK),
    hw.eventually (Metric.ball_mem_nhds H.endpoint (half_pos hdelta))] with i hi hdi
  intro hx E x hxle
  have hbig := hk (w i) (hballK (w i) hi)
  have hroot : 2 * transverseShortcutConstant W / delta <
      Real.sqrt (metricScalarAt g (w i)) := by
    rw [Real.lt_sqrt (div_nonneg
      (mul_nonneg (by norm_num) (transverseShortcutConstant_pos W).le) hdelta.le)]
    linarith
  have hdiam : transverseShortcutConstant W /
      Real.sqrt (metricScalarAt g (w i)) < delta / 2 := by
    apply (div_lt_iff₀ (Real.sqrt_pos.mpr E.Q_pos)).mpr
    have h := (div_lt_iff₀ hdelta).mp hroot
    nlinarith
  have hcenter : ∀ p : Sphere 2, E.F (p, 0) ∈ H.subend j := by
    intro p
    apply hball
    have hmem : E.F (p, 0) ∈ E.cross.tube.sectionSet (1 / 2) := by
      refine ⟨(p, 1 / 2), ⟨Set.mem_univ _, rfl⟩, ?_⟩
      exact E.cross.center_eq p
    have hnear := E.section_diameter_le (E.F (p, 0)) hmem
    have htri := dist_triangle (E.F (p, 0) : UniformSpace.Completion W)
      (w i : UniformSpace.Completion W) H.endpoint
    rw [UniformSpace.Completion.dist_eq, dist_comm (E.F (p, 0))] at htri
    have hsmall : _root_.Dist.dist (w i : UniformSpace.Completion W) H.endpoint < delta / 2 := hdi
    linarith
  by_contra hxnot
  exact (not_lt.mpr hxle) (E.cross.outer_side_of_center_in_subend g H j hcenter x hxnot)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_endChart_tip_side_subset_subend then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_endChart_tip_side_subset_subend"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_endChart_tip_side_subset_subend ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_endChart_tip_side_subset_subend

omit [SigmaCompactSpace W] in
theorem eventually_endChart_tip_side_radial_lt {g : SmoothRiemannianMetric I3 W}
    {ι : Type*} {l : Filter ι} (H : FiniteHorn g) (w : ι → W)
    (hw : Filter.Tendsto (fun i => (w i : UniformSpace.Completion W))
      l (nhds H.endpoint)) {R : ℝ} (hR : 0 < R) :
    ∀ᶠ i in l,
      ∀ (hx : w i ∈ H.subend (tailIndex g H))
        (E : EndChart g H (w i) hx), ∀ x : W,
        E.cross.tube.height x ≤ 1 / 2 →
          dist (x : UniformSpace.Completion W) H.endpoint < R := by
  obtain ⟨j, hj⟩ := finiteHorn_subend_radial_small g H hR
  filter_upwards [eventually_endChart_tip_side_subset_subend H w hw j] with i hi
  intro hx E x hxle
  exact hj x (hi hx E hxle)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_endChart_tip_side_radial_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_endChart_tip_side_radial_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_endChart_tip_side_radial_lt ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_endChart_tip_side_radial_lt


omit [SigmaCompactSpace W] in
theorem endRay_dist_lt_sum_of_scalar_radius_tendsto_atTop
    {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g)
    (ray : EndRay H.endpoint) (d : ℕ → ℝ)
    (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop) (a b : EndRay H.endpoint) :
    dist (a.point a.length) (b.point b.length) < a.length + b.length := by
  have hconv : Filter.Tendsto
      (fun i => (ray.point (d i) : UniformSpace.Completion W)) Filter.atTop
      (nhds H.endpoint) := by
    apply (tendsto_iff_dist_tendsto_zero).mpr
    simpa only [ray.radial _ (hd _)] using hzero
  have hR : 0 < _root_.Min.min a.length b.length / 2 :=
    half_pos (lt_min a.length_pos b.length_pos)
  obtain ⟨i, hi, hgood, hbig⟩ := ((eventually_endChart_tip_side_radial_lt H
    (fun i => ray.point (d i)) hconv hR).and
      ((eventually_mem_tail g H ray d hd hzero).and
        (hlarge.eventually_gt_atTop ((4 * transverseShortcutConstant W) ^ 2)))).exists
  let E := endChart g H (ray.point (d i)) hgood
  have hdiam : transverseShortcutConstant W /
      Real.sqrt (metricScalarAt g (ray.point (d i))) < d i / 4 := by
    have hspread : transverseShortcutConstant W /
        Real.sqrt (metricScalarAt g (ray.point (d i)) * d i ^ 2) < (1 / 2 : ℝ) / 2 := by
      apply sqrt_ratio_bound (transverseShortcutConstant_pos W) (by norm_num)
      have heq : (2 * transverseShortcutConstant W / (1 / 2 : ℝ)) ^ 2 =
          (4 * transverseShortcutConstant W) ^ 2 := by ring
      rw [heq]
      exact hbig
    have h := div_sqrt_lt_mul E.Q_pos (hd i).1 hspread
    linarith
  have houter (c : EndRay H.endpoint) (hRc : _root_.Min.min a.length b.length / 2 < c.length) :
      (1 / 2 : ℝ) < E.cross.tube.height (c.point c.length) := by
    apply lt_of_not_ge
    intro hc
    have h := hi hgood E (c.point c.length) hc
    rw [c.radial c.length ⟨c.length_pos, le_rfl⟩] at h
    linarith
  have haout : (1 / 2 : ℝ) < E.cross.tube.height (a.point a.length) :=
    houter a (by linarith [min_le_left a.length b.length])
  have hbout : (1 / 2 : ℝ) < E.cross.tube.height (b.point b.length) :=
    houter b (by linarith [min_le_right a.length b.length])
  obtain ⟨s, hs, p, hp⟩ := E.cross.endRay_meets_center g H a haout
  obtain ⟨t, ht, q, hq⟩ := E.cross.endRay_meets_center g H b hbout
  have hnear (c : EndRay H.endpoint) (u : ℝ) (v : Sphere 2)
      (hv : E.F (v, 0) = c.point u) :
      _root_.Dist.dist (ray.point (d i)) (c.point u) ≤ transverseShortcutConstant W /
        Real.sqrt (metricScalarAt g (ray.point (d i))) := by
    apply E.section_diameter_le
    refine ⟨(v, 1 / 2), ⟨Set.mem_univ _, rfl⟩, ?_⟩
    rw [E.cross.center_eq, hv]
  have has := hnear a s p hp
  have hbt := hnear b t q hq
  have hsrad : d i - _root_.Dist.dist (ray.point (d i)) (a.point s) ≤ s := by
    have h := dist_triangle (ray.point (d i) : UniformSpace.Completion W)
      (a.point s : UniformSpace.Completion W) H.endpoint
    rw [UniformSpace.Completion.dist_eq, ray.radial _ (hd i), a.radial s hs] at h
    linarith
  have htrad : d i - _root_.Dist.dist (ray.point (d i)) (b.point t) ≤ t := by
    have h := dist_triangle (ray.point (d i) : UniformSpace.Completion W)
      (b.point t : UniformSpace.Completion W) H.endpoint
    rw [UniformSpace.Completion.dist_eq, ray.radial _ (hd i), b.radial t ht] at h
    linarith
  have hshort : _root_.Dist.dist (a.point s) (b.point t) < s + t := by
    have htri := dist_triangle (a.point s) (ray.point (d i)) (b.point t)
    rw [dist_comm (a.point s) (ray.point (d i))] at htri
    linarith [hd i |>.1]
  have hleft : _root_.Dist.dist (a.point a.length) (a.point s) = a.length - s := by
    rw [a.minimizing a.length ⟨a.length_pos, le_rfl⟩ s hs,
      abs_of_nonneg (sub_nonneg.mpr hs.2)]
  have hright : _root_.Dist.dist (b.point t) (b.point b.length) = b.length - t := by
    rw [b.minimizing t ht b.length ⟨b.length_pos, le_rfl⟩,
      abs_of_nonpos (sub_nonpos.mpr ht.2)]
    ring
  have htri1 := dist_triangle (a.point a.length) (a.point s) (b.point b.length)
  have htri2 := dist_triangle (a.point s) (b.point t) (b.point b.length)
  rw [hleft] at htri1
  rw [hright] at htri2
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRay_dist_lt_sum_of_scalar_radius_tendsto_atTop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRay_dist_lt_sum_of_scalar_radius_tendsto_atTop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRay_dist_lt_sum_of_scalar_radius_tendsto_atTop ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRay_dist_lt_sum_of_scalar_radius_tendsto_atTop

omit [SigmaCompactSpace W] in
theorem endRay_point_dist_div_tendsto_zero_of_scalar_radius_tendsto_atTop
    {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g)
    (ray : EndRay H.endpoint) (d : ℕ → ℝ)
    (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop) (a : EndRay H.endpoint) :
    Filter.Tendsto (fun i => _root_.Dist.dist (ray.point (d i)) (a.point (d i)) / d i)
      Filter.atTop (nhds 0) := by
  have hconv : Filter.Tendsto
      (fun i => (ray.point (d i) : UniformSpace.Completion W)) Filter.atTop
      (nhds H.endpoint) := by
    apply (tendsto_iff_dist_tendsto_zero).mpr
    simpa only [ray.radial _ (hd _)] using hzero
  rw [Metric.tendsto_nhds]
  intro eps heps
  filter_upwards [eventually_endChart_tip_side_radial_lt H (fun i => ray.point (d i)) hconv
      (half_pos a.length_pos), eventually_mem_tail g H ray d hd hzero,
    hzero.eventually (eventually_lt_nhds a.length_pos),
    hlarge.eventually_gt_atTop ((2 * transverseShortcutConstant W / eps) ^ 2)]
      with i htip hgood hdlen hbig
  let E := endChart g H (ray.point (d i)) hgood
  have hdiam : transverseShortcutConstant W /
      Real.sqrt (metricScalarAt g (ray.point (d i))) < d i * (eps / 2) := by
    apply div_sqrt_lt_mul E.Q_pos (hd i).1
    exact sqrt_ratio_bound (transverseShortcutConstant_pos W) heps hbig
  have haout : (1 / 2 : ℝ) < E.cross.tube.height (a.point a.length) := by
    apply lt_of_not_ge
    intro ha
    have h := htip hgood E (a.point a.length) ha
    rw [a.radial a.length ⟨a.length_pos, le_rfl⟩] at h
    linarith [a.length_pos]
  obtain ⟨s, hs, p, hp⟩ := E.cross.endRay_meets_center g H a haout
  have hnear : _root_.Dist.dist (ray.point (d i)) (a.point s) ≤ transverseShortcutConstant W /
      Real.sqrt (metricScalarAt g (ray.point (d i))) := by
    apply E.section_diameter_le
    refine ⟨(p, 1 / 2), ⟨Set.mem_univ _, rfl⟩, ?_⟩
    rw [E.cross.center_eq, hp]
  have hds : |d i - s| ≤ _root_.Dist.dist (ray.point (d i)) (a.point s) := by
    have h := abs_dist_sub_le (ray.point (d i) : UniformSpace.Completion W)
      (a.point s : UniformSpace.Completion W) H.endpoint
    rwa [UniformSpace.Completion.dist_eq, ray.radial _ (hd i), a.radial s hs] at h
  have htri := dist_triangle (ray.point (d i)) (a.point s) (a.point (d i))
  rw [a.minimizing s hs (d i) ⟨(hd i).1, hdlen.le⟩, abs_sub_comm s (d i)] at htri
  have hbound : _root_.Dist.dist (ray.point (d i)) (a.point (d i)) / d i < eps := by
    apply (div_lt_iff₀ (hd i).1).mpr
    nlinarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg dist_nonneg (hd i).1.le)]
  exact hbound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRay_point_dist_div_tendsto_zero_of_scalar_radius_tendsto_atTop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRay_point_dist_div_tendsto_zero_of_scalar_radius_tendsto_atTop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRay_point_dist_div_tendsto_zero_of_scalar_radius_tendsto_atTop ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRay_point_dist_div_tendsto_zero_of_scalar_radius_tendsto_atTop

omit [SigmaCompactSpace W] in
theorem endComparisonAngle_tendsto_zero_of_scalar_radius_tendsto_atTop
    {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g)
    (ray : EndRay H.endpoint) (d : ℕ → ℝ)
    (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop) (a : EndRay H.endpoint) :
    Filter.Tendsto (fun i => endComparisonAngle ray a (d i) (d i))
      Filter.atTop (nhds 0) := by
  have hdist := endRay_point_dist_div_tendsto_zero_of_scalar_radius_tendsto_atTop
    H ray d hd hzero hlarge a
  have harg : Filter.Tendsto
      (fun i => 1 - (_root_.Dist.dist (ray.point (d i)) (a.point (d i)) / d i) ^ 2 / 2)
      Filter.atTop (nhds 1) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div, sub_zero] using
      ((tendsto_const_nhds (x := (1 : ℝ))).sub ((hdist.pow 2).div_const 2))
  have hlim := Real.continuous_arccos.continuousAt.tendsto.comp harg
  have heq : (fun i => endComparisonAngle ray a (d i) (d i)) =
      (fun i => Real.arccos (1 - (_root_.Dist.dist (ray.point (d i)) (a.point (d i)) / d i) ^ 2 / 2)) := by
    funext i
    unfold endComparisonAngle
    congr 1
    field_simp [(hd i).1.ne']
    ring
  rw [heq]
  convert! hlim using 1
  rw [Real.arccos_one]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endComparisonAngle_tendsto_zero_of_scalar_radius_tendsto_atTop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endComparisonAngle_tendsto_zero_of_scalar_radius_tendsto_atTop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endComparisonAngle_tendsto_zero_of_scalar_radius_tendsto_atTop ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endComparisonAngle_tendsto_zero_of_scalar_radius_tendsto_atTop


omit [SigmaCompactSpace W] in
private theorem endRay_point_eq_of_scalar_radius_tendsto_atTop
    {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g)
    (ray : EndRay H.endpoint) (d : ℕ → ℝ)
    (hd : ∀ i, d i ∈ _root_.Set.Ioc 0 ray.length)
    (hzero : _root_.Filter.Tendsto d _root_.Filter.atTop (nhds 0))
    (hlarge : _root_.Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2) _root_.Filter.atTop _root_.Filter.atTop)
    {D : ℝ} (hmono : ∀ a b : EndRay H.endpoint,
      CoordinatewiseNonincreasingOn (endRayLength H.endpoint D a) (endRayLength H.endpoint D b)
        (radialComparisonAngle (endRayFamily H.endpoint) a b))
    (a : EndRay H.endpoint) {s : ℝ}
    (hsray : s ∈ _root_.Set.Ioc 0 (_root_.Min.min ray.length D)) (hsa : s ≤ a.length) :
    ray.point s = a.point s := by
  have hsA : s ∈ _root_.Set.Ioc 0 (_root_.Min.min a.length D) := ⟨hsray.1, le_min hsa (hsray.2.trans (min_le_right _ _))⟩
  have hevent : ∀ᶠ i in _root_.Filter.atTop,
      endComparisonAngle ray a s s ≤ endComparisonAngle ray a (d i) (d i) := by
    filter_upwards [hzero.eventually (eventually_lt_nhds hsray.1)] with i hi
    have hiR : d i ∈ _root_.Set.Ioc 0 (endRayLength H.endpoint D ray) :=
      ⟨(hd i).1, hi.le.trans hsray.2⟩
    have hiA : d i ∈ _root_.Set.Ioc 0 (endRayLength H.endpoint D a) :=
      ⟨(hd i).1, hi.le.trans hsA.2⟩
    have h1 := (hmono ray a).1 hiR hsray hsA hi.le
    have h2 := (hmono ray a).2 hiR hiA hsA hi.le
    simpa only [radialComparisonAngle_endRay] using h1.trans h2
  have hangle : endComparisonAngle ray a s s ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds
      (endComparisonAngle_tendsto_zero_of_scalar_radius_tendsto_atTop H ray d hd hzero hlarge a)
      hevent
  have hupper : _root_.Dist.dist (ray.point s) (a.point s) ≤ s + s := by
    have h := dist_triangle (ray.point s : UniformSpace.Completion W) H.endpoint
      (a.point s : UniformSpace.Completion W)
    rw [UniformSpace.Completion.dist_eq, ray.radial s ⟨hsray.1, hsray.2.trans (min_le_left _ _)⟩,
      dist_comm H.endpoint, a.radial s ⟨hsray.1, hsa⟩] at h
    exact h
  have hsquare := sq_le_cos_of_comparisonAngle_le hsray.1 hsray.1
    (by simp) hupper
    Real.pi_pos.le hangle
  rw [Real.cos_zero] at hsquare
  apply dist_eq_zero.mp
  nlinarith [dist_nonneg (x := ray.point s) (y := a.point s)]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRay_point_eq_of_scalar_radius_tendsto_atTop
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRay_point_eq_of_scalar_radius_tendsto_atTop target :: scope.openDecls } }

omit [SigmaCompactSpace W] in
theorem hornRadialExitPositionAtEndChart_of_scalar_radius_tendsto_atTop
    {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g)
    (ray : EndRay H.endpoint) (d : ℕ → ℝ)
    (hd : ∀ i, d i ∈ _root_.Set.Ioc 0 ray.length)
    (hzero : _root_.Filter.Tendsto d _root_.Filter.atTop (nhds 0))
    (hlarge : _root_.Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2) _root_.Filter.atTop _root_.Filter.atTop) :
    HornRadialExitPositionAtEndChart g H ray d := by
  let : LocallyCompactSpace H.tube.map.source := H.tube.map.open_source.locallyCompactSpace
  have hsource : IsSigmaCompact H.tube.map.source :=
    isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
  have himage := hsource.image_of_continuousOn H.tube.map.contMDiffOn_toFun.continuousOn
  rw [H.tube.map.toPartialEquiv.image_source_eq_target, H.tube.target_eq] at himage
  let : SigmaCompactSpace W := isSigmaCompact_univ_iff.mp himage
  obtain ⟨D, hD, hmono⟩ := finiteHorn_end_angle_monotone_of_endRay_dist_lt_sum g H
    (endRay_dist_lt_sum_of_scalar_radius_tendsto_atTop H ray d hd hzero hlarge)
  obtain ⟨rho, hrho, hrays⟩ := finiteHorn_exists_intrinsic_endRay_near_endpoint g H
  let T : ℝ := _root_.Min.min ray.length D / 2
  have hT : 0 < T := half_pos (lt_min ray.length_pos hD)
  have hTlen : T ≤ ray.length :=
    (half_le_self (lt_min ray.length_pos hD).le).trans (min_le_left _ _)
  have hTD : T ≤ D :=
    (half_le_self (lt_min ray.length_pos hD).le).trans (min_le_right _ _)
  have hconv : _root_.Filter.Tendsto (fun i => (ray.point (d i) : UniformSpace.Completion W)) _root_.Filter.atTop
      (nhds H.endpoint) := by
    apply (tendsto_iff_dist_tendsto_zero).mpr
    simpa only [ray.radial _ (hd _)] using hzero
  intro e he he10
  filter_upwards [eventually_endChart_tip_side_radial_lt H (fun i => ray.point (d i)) hconv
      (lt_min hT hrho),
    hlarge.eventually_gt_atTop ((2 * transverseShortcutConstant W / e) ^ 2)] with i htip hbig
  intro hx x hxrad
  let E := endChart g H (ray.point (d i)) hx
  by_contra hxnot
  have hxle : E.cross.tube.height x ≤ 1 / 2 := le_of_not_gt hxnot
  let r : ℝ := _root_.Dist.dist (x : UniformSpace.Completion W) H.endpoint
  have hr : 0 < r := dist_pos.mpr (H.endpoint_missing x)
  have hrsmall : r < _root_.Min.min T rho := htip hx E x hxle
  obtain ⟨a, ha⟩ := hrays x (hrsmall.trans_le (min_le_right _ _))
  have hlength : a.length = r := by
    have h := a.radial a.length ⟨a.length_pos, le_rfl⟩
    rw [ha] at h
    exact h.symm
  have hxray : ray.point r = x := by
    have h := endRay_point_eq_of_scalar_radius_tendsto_atTop H ray d hd hzero hlarge hmono a
      (s := r) ⟨hr, le_min ((hrsmall.trans_le (min_le_left _ _)).le.trans hTlen)
        ((hrsmall.trans_le (min_le_left _ _)).le.trans hTD)⟩ (by rw [hlength])
    calc ray.point r = a.point r := h
      _ = x := by rw [← hlength, ha]
  have hout : (1 / 2 : ℝ) < E.cross.tube.height (ray.point T) := by
    apply lt_of_not_ge
    intro hle
    have h := htip hx E (ray.point T) hle
    rw [ray.radial T ⟨hT, hTlen⟩] at h
    exact (not_lt_of_ge (min_le_left _ _)) h
  have hLip : LipschitzOnWith 1 ray.point (_root_.Set.Ioc (0 : ℝ) ray.length) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    simpa only [ray.minimizing s hs t ht, NNReal.coe_one, one_mul, Real.dist_eq] using
      (le_rfl : |s - t| ≤ |s - t|)
  have hrT : r ≤ T := (hrsmall.trans_le (min_le_left _ _)).le
  have hcont : ContinuousOn (E.cross.tube.height ∘ ray.point) (_root_.Set.Icc r T) :=
    E.cross.tube.continuous_height.comp_continuousOn
      (hLip.continuousOn.mono (fun u hu => ⟨hr.trans_le hu.1, hu.2.trans hTlen⟩))
  obtain ⟨u, hu, hlevel⟩ := intermediate_value_Icc hrT hcont
    (show (1 / 2 : ℝ) ∈ _root_.Set.Icc ((E.cross.tube.height ∘ ray.point) r)
      ((E.cross.tube.height ∘ ray.point) T) from by
      simpa only [Function.comp_apply, hxray, _root_.Set.mem_Icc] using And.intro hxle hout.le)
  have hmem : ray.point u ∈ E.cross.tube.sectionSet (1 / 2) :=
    (E.cross.tube.mem_sectionSet_iff (by norm_num) (ray.point u)).mpr hlevel
  have hdist := E.section_diameter_le (ray.point u) hmem
  have hdiam : transverseShortcutConstant W /
      Real.sqrt (metricScalarAt g (ray.point (d i))) < d i * (e / 2) :=
    div_sqrt_lt_mul E.Q_pos (hd i).1
      (sqrt_ratio_bound (transverseShortcutConstant_pos W) he hbig)
  have htri := dist_triangle (ray.point u : UniformSpace.Completion W)
    (ray.point (d i) : UniformSpace.Completion W) H.endpoint
  rw [UniformSpace.Completion.dist_eq, ray.radial u ⟨hr.trans_le hu.1, hu.2.trans hTlen⟩,
    ray.radial _ (hd i), dist_comm (ray.point u) (ray.point (d i))] at htri
  change (1 + e) * d i < r at hxrad
  nlinarith [hu.1, (hd i).1]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornRadialExitPositionAtEndChart_of_scalar_radius_tendsto_atTop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornRadialExitPositionAtEndChart_of_scalar_radius_tendsto_atTop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornRadialExitPositionAtEndChart_of_scalar_radius_tendsto_atTop ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornRadialExitPositionAtEndChart_of_scalar_radius_tendsto_atTop

end

theorem finite_horn_barriers {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (endData : EndGeometry H) (ray : EndRay H.endpoint)
    (d : ℕ → ℝ) (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop) : Nonempty (HornBarriers H ray d) := by
  exact finite_horn_barriers_of_hornRadialExitPositionAtEndChart H endData ray d hd hzero hlarge
    (hornRadialExitPositionAtEndChart_of_scalar_radius_tendsto_atTop H ray d hd hzero hlarge)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_barriers then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_barriers"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_barriers ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_barriers

structure ScaleCurvatureUpperBound {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g)
    (ray : EndRay H.endpoint) (d : ℕ → ℝ) : Prop where
  upper : ∃ C : ℝ, 0 < C ∧ ∀ᶠ i in Filter.atTop,
    metricScalarAt g (ray.point (d i)) * d i ^ 2 ≤ C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ScaleCurvatureUpperBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ScaleCurvatureUpperBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ScaleCurvatureUpperBound ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ScaleCurvatureUpperBound

omit [SigmaCompactSpace W] in
theorem finite_horn_two_scale_comparison {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (_endData : EndGeometry H) (_angles : EndAngles H)
    (ray : EndRay H.endpoint) (d : ℕ → ℝ) (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hupper : ScaleCurvatureUpperBound H ray d) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ᶠ i in Filter.atTop,
      c ≤ metricScalarAt g (ray.point (d i)) * d i ^ 2 ∧
      metricScalarAt g (ray.point (d i)) * d i ^ 2 ≤ C :=
  finite_horn_two_scale_comparison_of_upper_bound H ray d hd hzero hupper.upper

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_two_scale_comparison then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_two_scale_comparison"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_two_scale_comparison ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_two_scale_comparison

structure ConeFlowLimit (X : FlowSequence.{u}) where
  delta : ℝ
  delta_pos : 0 < delta
  flow : PointedFlowData.{u, 0, 0} I3 (RealTimeInterval.closed (-delta) 0 (by linarith))
  patch : Set flow.M
  open_patch : IsOpen patch
  compact_patch : IsCompact (closure patch)
  connected_patch : IsConnected patch
  base_mem : flow.basepoint ∈ patch
  cone : ConeChart (flow.S.base.metric 0) patch
  nonnegative : ∀ s ∈ Set.Icc (-delta) 0, SecLower (flow.S.base.metric s) 0 patch
  normalized : PointedFlowScalarAtBase flow 1
  subseq : ℕ → ℕ
  strictMono : StrictMono subseq
  scale : ℕ → ℝ
  scale_pos : ∀ i, 0 < scale i
  scale_tendsto : Filter.Tendsto scale Filter.atTop Filter.atTop
  map : ∀ i, PartialDiffeomorph I3 I3 flow.M (X.term (subseq i)).M ∞
  contains_patch : ∀ i, patch ⊆ (map i).source
  window : ∀ᶠ i in Filter.atTop,
    Set.Icc (-delta / scale i) 0 ⊆ (X.interval (subseq i)).carrier
  converges : ∀ K : Set flow.M, IsCompact K → K ⊆ patch →
    ∀ m : ℕ, ∀ eps : ℝ, 0 < eps → ∀ᶠ i in Filter.atTop,
      Nonempty (MetricComparisonOn (fun s => flow.S.base.metric s)
        (rescaledMetric (X.term (subseq i)).S 0 (scale i) (scale_pos i))
        (map i) K (Set.Icc (-delta) 0) m eps)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ConeFlowLimit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ConeFlowLimit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ConeFlowLimit ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ConeFlowLimit

theorem cone_terminal_exclusion {delta : ℝ} (hd : 0 < delta)
    (P : PointedFlowData.{u, 0, 0} I3 (RealTimeInterval.closed (-delta) 0 (by linarith)))
    (U : Set P.M) (_hU : IsOpen U) (cone : ConeChart (P.S.base.metric 0) U)
    (hsec : ∀ s ∈ Set.Icc (-delta) 0, SecLower (P.S.base.metric s) 0 U)
    (hnonflat : ∃ x ∈ U, metricScalarAt (P.S.base.metric 0) x ≠ 0) : False := by
  exact solution_cone_terminal_exclusion P.S P.isSolution (neg_lt_zero.mpr hd)
    (fun _ h => h) (fun _ h => h) U cone hsec hnonflat

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cone_terminal_exclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cone_terminal_exclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cone_terminal_exclusion ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cone_terminal_exclusion

structure RealizedFiniteHorn (X : FlowSequence.{u}) where
  space : Type u
  [metric_space : MetricSpace space]
  [charted : ChartedSpace ThreeSpace space]
  [smooth : IsManifold I3 ∞ space]
  [sigmaCompact : SigmaCompactSpace space]
  metric : SmoothRiemannianMetric I3 space
  horn : FiniteHorn metric
  subseq : ℕ → ℕ
  strictMono : StrictMono subseq
  maps : ∀ i, PartialDiffeomorph I3 I3 space (X.term (subseq i)).M ∞
  exhaustion : ExhaustsByOpen (fun i => (maps i).source)
  convergence : ∀ K : Set space, IsCompact K → ∀ m : ℕ, ∀ eta : ℝ, 0 < eta →
    ∀ᶠ i in Filter.atTop, K ⊆ (maps i).source ∧
      Nonempty (MetricComparisonOn (fun _ => metric)
        (fun _ => (X.term (subseq i)).S.base.metric 0) (maps i) K {0} m eta)
  radii : ℕ → ℝ
  radii_mem : ∀ i, radii i ∈ Set.Ioc 0 horn.axial.length
  radii_zero : Filter.Tendsto radii Filter.atTop (nhds 0)
  directionNet : ScaleDirectionNet metric horn
  separatedRays : ScaleSeparatedEndRays metric horn
  coneRealization : ∀ (angles : EndAngles horn) (ray : EndRay horn.endpoint) (d : ℕ → ℝ),
    (∀ i, d i ∈ Set.Ioc 0 ray.length) → Filter.Tendsto d Filter.atTop (nhds 0) →
    ConeDistanceRealization horn angles ray d
  depth_ok : hornDepthThreshold.{u} ≤ horn.collar_depth
  curvatureUpper : ScaleCurvatureUpperBound horn horn.axial radii

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.RealizedFiniteHorn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.RealizedFiniteHorn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.RealizedFiniteHorn ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.RealizedFiniteHorn

attribute [local instance] RealizedFiniteHorn.metric_space RealizedFiniteHorn.charted
  RealizedFiniteHorn.smooth RealizedFiniteHorn.sigmaCompact

namespace RealizedFiniteHorn

theorem end_rays {X : FlowSequence.{u}} (H : RealizedFiniteHorn X) :
    Nonempty (EndGeometry H.horn) :=
  finite_horn_end_rays H.horn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.RealizedFiniteHorn.end_rays then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.RealizedFiniteHorn.end_rays"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.RealizedFiniteHorn.end_rays ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.RealizedFiniteHorn.end_rays

theorem ray_approximation {X : FlowSequence.{u}} (H : RealizedFiniteHorn X)
    (endData : EndGeometry H.horn) :
    ∃ d : ℝ, 0 < d ∧ ∀ a b : EndRay H.horn.endpoint,
      ∀ lo hi : Fin 2 → ℝ, (∀ k, 0 < lo k) → (∀ k, lo k ≤ hi k) →
      hi 0 ≤ a.length → hi 1 ≤ b.length → (∀ k, hi k ≤ d) →
      Nonempty (RayApproximation H.horn a b lo hi) :=
  finite_horn_ray_approximation H.horn endData
    (le_trans hornEndGeometryDepth_le_hornDepthThreshold.{u} H.depth_ok)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.RealizedFiniteHorn.ray_approximation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.RealizedFiniteHorn.ray_approximation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.RealizedFiniteHorn.ray_approximation ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.RealizedFiniteHorn.ray_approximation

theorem end_angle {X : FlowSequence.{u}} (H : RealizedFiniteHorn X)
    (endData : EndGeometry H.horn) : Nonempty (EndAngles H.horn) :=
  finite_horn_end_angle H.horn endData
    (le_trans hornEndGeometryDepth_le_hornDepthThreshold.{u} H.depth_ok)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.RealizedFiniteHorn.end_angle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.RealizedFiniteHorn.end_angle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.RealizedFiniteHorn.end_angle ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.RealizedFiniteHorn.end_angle

theorem direction_compactness {X : FlowSequence.{u}} (H : RealizedFiniteHorn X)
    (endData : EndGeometry H.horn) (angles : EndAngles H.horn) :
    letI := angles.metric
    TotallyBounded (Set.univ : Set angles.quotient) ∧
      CompactSpace (UniformSpace.Completion angles.quotient) ∧
      ∃ a b : EndRay H.horn.endpoint, 0 < angles.angle a b :=
  finite_horn_direction_compactness H.horn endData angles H.directionNet H.separatedRays

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.RealizedFiniteHorn.direction_compactness then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.RealizedFiniteHorn.direction_compactness"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.RealizedFiniteHorn.direction_compactness ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.RealizedFiniteHorn.direction_compactness

theorem cone_convergence {X : FlowSequence.{u}} (H : RealizedFiniteHorn X)
    (endData : EndGeometry H.horn) (angles : EndAngles H.horn)
    (ray : EndRay H.horn.endpoint) (d : ℕ → ℝ) (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0)) :
    Nonempty (AnnularConvergence H.horn angles ray d) :=
  finite_horn_cone_convergence H.horn endData angles ray d hd hzero
    (H.coneRealization angles ray d hd hzero)
    (le_trans hornEndGeometryDepth_le_hornDepthThreshold.{u} H.depth_ok)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.RealizedFiniteHorn.cone_convergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.RealizedFiniteHorn.cone_convergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.RealizedFiniteHorn.cone_convergence ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.RealizedFiniteHorn.cone_convergence

theorem two_scale_comparison {X : FlowSequence.{u}} (H : RealizedFiniteHorn X)
    (endData : EndGeometry H.horn) (angles : EndAngles H.horn) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ᶠ i in Filter.atTop,
      c ≤ metricScalarAt H.metric (H.horn.axial.point (H.radii i)) * H.radii i ^ 2 ∧
      metricScalarAt H.metric (H.horn.axial.point (H.radii i)) * H.radii i ^ 2 ≤ C :=
  finite_horn_two_scale_comparison H.horn endData angles H.horn.axial H.radii
    H.radii_mem H.radii_zero H.curvatureUpper

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.RealizedFiniteHorn.two_scale_comparison then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.RealizedFiniteHorn.two_scale_comparison"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.RealizedFiniteHorn.two_scale_comparison ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.RealizedFiniteHorn.two_scale_comparison

end RealizedFiniteHorn

theorem ConeFlowLimit.scalar_eq_zero {X : FlowSequence.{u}} (C : ConeFlowLimit X) :
    ∀ x ∈ C.patch, metricScalarAt (C.flow.S.base.metric 0) x = 0 := by
  by_contra hcon
  simp only [_root_.Classical.not_forall] at hcon
  obtain ⟨x, hx, hne⟩ := hcon
  exact cone_terminal_exclusion C.delta_pos C.flow C.patch C.open_patch C.cone
    C.nonnegative ⟨x, hx, hne⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ConeFlowLimit
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ConeFlowLimit.scalar_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ConeFlowLimit.scalar_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ConeFlowLimit.scalar_eq_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ConeFlowLimit.scalar_eq_zero

theorem ConeFlowLimit.false {X : FlowSequence.{u}} (C : ConeFlowLimit X) : False := by
  have hzero : metricScalarAt (C.flow.S.base.metric 0) C.flow.basepoint = 0 :=
    C.scalar_eq_zero C.flow.basepoint C.base_mem
  have hone : metricScalarAt (C.flow.S.base.metric 0) C.flow.basepoint = 1 := by
    simpa only [PointedFlowScalarAtBase, SolutionOn.scalar, SolutionFamily.scalar] using C.normalized
  rw [hzero] at hone
  exact zero_ne_one hone

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ConeFlowLimit.false then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ConeFlowLimit.false"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ConeFlowLimit.false ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ConeFlowLimit.false

theorem coneFlowLimit_not_nonempty {X : FlowSequence.{u}} : ¬ Nonempty (ConeFlowLimit X) :=
  fun h => h.elim ConeFlowLimit.false

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.coneFlowLimit_not_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.coneFlowLimit_not_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.coneFlowLimit_not_nonempty ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.coneFlowLimit_not_nonempty

theorem finiteControlledRadius_false_of_boundedAtDistance {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (hb : BoundedAtDistance X)
    (hradius : FiniteControlledRadius X) : False := by
  obtain ⟨C, hC⟩ := hb (2 * hradius.radius) (by linarith [hradius.radius_pos])
  have hcurve : Filter.Tendsto
      (fun i => metricScalarAt ((X.term i).S.base.metric 0) (hradius.points i))
      Filter.atTop Filter.atTop := by
    simpa only [SolutionOn.scalar, SolutionFamily.scalar] using hradius.curvature_limit
  have hlarge : ∀ᶠ i in Filter.atTop,
      C < metricScalarAt ((X.term i).S.base.metric 0) (hradius.points i) :=
    hcurve.eventually_gt_atTop C
  have hsmall : ∀ᶠ i in Filter.atTop,
      metricScalarAt ((X.term i).S.base.metric 0) (hradius.points i) ≤ C := by
    filter_upwards [hradius.distance_limit.eventually
      (eventually_lt_nhds (show hradius.radius < 2 * hradius.radius by
        linarith [hradius.radius_pos]))]
      with i hi
    exact hC i (hradius.points i) hi.le
  obtain ⟨i, hi₁, hi₂⟩ := (hlarge.and hsmall).exists
  exact absurd hi₁ (not_lt.mpr hi₂)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteControlledRadius_false_of_boundedAtDistance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteControlledRadius_false_of_boundedAtDistance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteControlledRadius_false_of_boundedAtDistance ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteControlledRadius_false_of_boundedAtDistance

theorem finite_horn_construction {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hkappa : 0 < kappa) (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi) :
    ∃ alphaMax collarMin : ℝ, 0 < alphaMax ∧ alphaMax < 1 / 11 ∧ 0 < collarMin ∧
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaMax → ∀ collar : ℝ, collarMin ≤ collar →
        ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            FiniteControlledRadius X → ∃ H : RealizedFiniteHorn X.toFlowSequence,
              H.horn.neck_precision = alpha ∧ collar ≤ H.horn.collar_depth := by
  obtain ⟨epsStar, hepsStar, hbound⟩ := exists_boundedAtDistance.{u} hkappa
  refine ⟨1 / 20, 1, by norm_num, by norm_num, one_pos, ?_⟩
  intro alpha halpha halphaMax collar hcollar
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle X hradius
  exact (finiteControlledRadius_false_of_boundedAtDistance X
    (hbound eps heps hle sigma hsigma Phi hPhi X) hradius).elim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_construction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_construction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_construction ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_construction

theorem finite_horn_smooth_cone_patch {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (hkappa : 0 < kappa)
    (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi)
    (H : RealizedFiniteHorn X.toFlowSequence) (endData : EndGeometry H.horn)
    (angles : EndAngles H.horn)
    (annuli : AnnularConvergence H.horn angles H.horn.axial H.radii)
    (bounds : ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ᶠ i in Filter.atTop,
      c ≤ metricScalarAt H.metric (H.horn.axial.point (H.radii i)) * H.radii i ^ 2 ∧
      metricScalarAt H.metric (H.horn.axial.point (H.radii i)) * H.radii i ^ 2 ≤ C) :
    ¬ Nonempty (ConeFlowLimit X.toFlowSequence) := by
  let _ := hkappa
  let _ := hsigma
  let _ := hPhi
  let _ := H
  let _ := endData
  let _ := angles
  let _ := annuli
  let _ := bounds
  exact coneFlowLimit_not_nonempty

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_smooth_cone_patch then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_smooth_cone_patch"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_smooth_cone_patch ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_smooth_cone_patch

theorem finite_horn_produces_cone {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hkappa : 0 < kappa) (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        FiniteControlledRadius X → ¬ Nonempty (ConeFlowLimit X.toFlowSequence) := by
  let _ := hkappa
  let _ := hsigma
  let _ := hPhi
  exact ⟨1, one_pos, fun _ _ _ _ _ => coneFlowLimit_not_nonempty⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_produces_cone then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_produces_cone"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_produces_cone ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_produces_cone


def TerminalParabolicCurvatureBound {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (start : ℝ) : Prop :=
  ∀ rho : ℝ, 0 < rho → ∃ curvature radius : ℝ, 0 < curvature ∧ 0 < radius ∧
    (∀ i, ∀ t ∈ Set.Icc start 0, ∀ y : (X.term i).M,
      riemannianEDistOf (I := I3) ((X.term i).S.base.metric start) (X.term i).basepoint y ≤
        ENNReal.ofReal (radius / Real.sqrt curvature) →
      curvDerivNormSq (I := I3) 0 ((X.term i).S.base.metric t) y ≤ curvature ^ 2) ∧
    (∀ i, ∀ y : (X.term i).M,
      metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y ≤ rho →
      riemannianEDistOf (I := I3) ((X.term i).S.base.metric start) (X.term i).basepoint y ≤
        ENNReal.ofReal (radius / (2 * Real.sqrt curvature)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalParabolicCurvatureBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalParabolicCurvatureBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalParabolicCurvatureBound ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalParabolicCurvatureBound

theorem terminalParabolicCurvatureControl_of_bound
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (heps : 0 < eps) (h : TerminalParabolicCurvatureBound X (-(modelDepth eps))) :
    TerminalParabolicCurvatureControl X (-(modelDepth eps)) := by
  intro rho hrho
  obtain ⟨curvature, radius, hK, hR, hcurv, hcover⟩ := h rho hrho
  refine ⟨curvature, radius, hK, hR, ?_, hcurv, hcover⟩
  intro i
  have hm0 : 0 < modelDepth eps := by
    simp only [modelDepth]
    exact inv_pos.mpr heps
  have hm : -(modelDepth eps) ∈ (X.interval i).carrier :=
    (normalizedSequence_modelDepth_window X heps i).1 ⟨le_rfl, by linarith⟩
  have hcomplete : RiemannianMetricComplete (I := I3)
      ((X.term i).S.base.metric (-(modelDepth eps))) :=
    ⟨X.complete i (-(modelDepth eps)) hm⟩
  exact hcomplete.closedEBall_isCompact (X.term i).basepoint (radius / Real.sqrt curvature)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalParabolicCurvatureControl_of_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalParabolicCurvatureControl_of_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalParabolicCurvatureControl_of_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalParabolicCurvatureControl_of_bound

theorem bounded_curvature_at_distance_of_terminalParabolicCurvatureControl
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        TerminalParabolicCurvatureControl X (-(modelDepth eps))) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        BoundedAtDistance X ∧ TerminalDerivativeBounds X := by
  obtain ⟨e, he, hctl⟩ := h
  refine ⟨e, he, ?_⟩
  intro eps hp hle X
  exact bounded_curvature_at_distance_of_parabolicCurvatureBounds X
    (parabolicCurvatureBoundsAtBase_of_terminalParabolicCurvatureControl X hp
      (hctl eps hp hle X))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.bounded_curvature_at_distance_of_terminalParabolicCurvatureControl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.bounded_curvature_at_distance_of_terminalParabolicCurvatureControl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.bounded_curvature_at_distance_of_terminalParabolicCurvatureControl ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.bounded_curvature_at_distance_of_terminalParabolicCurvatureControl

theorem bounded_curvature_at_distance_of_terminalParabolicCurvatureBound
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        TerminalParabolicCurvatureBound X (-(modelDepth eps))) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        BoundedAtDistance X ∧ TerminalDerivativeBounds X :=
  bounded_curvature_at_distance_of_terminalParabolicCurvatureControl (by
    obtain ⟨e, he, hb⟩ := h
    exact ⟨e, he, fun eps hp hle X => terminalParabolicCurvatureControl_of_bound X hp (hb eps hp hle X)⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.bounded_curvature_at_distance_of_terminalParabolicCurvatureBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.bounded_curvature_at_distance_of_terminalParabolicCurvatureBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.bounded_curvature_at_distance_of_terminalParabolicCurvatureBound ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.bounded_curvature_at_distance_of_terminalParabolicCurvatureBound

abbrev TerminalParabolicCurvatureBoundProducer.{v} (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ X : NormalizedSequence.{v} eps kappa sigma Phi,
      TerminalParabolicCurvatureBound X (-(modelDepth eps))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalParabolicCurvatureBoundProducer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalParabolicCurvatureBoundProducer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalParabolicCurvatureBoundProducer ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalParabolicCurvatureBoundProducer

theorem bounded_curvature_at_distance_of_terminalParabolicCurvatureBoundProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : TerminalParabolicCurvatureBoundProducer.{u} kappa sigma Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        BoundedAtDistance X ∧ TerminalDerivativeBounds X := by
  unfold TerminalParabolicCurvatureBoundProducer at h
  exact bounded_curvature_at_distance_of_terminalParabolicCurvatureBound h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.bounded_curvature_at_distance_of_terminalParabolicCurvatureBoundProducer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.bounded_curvature_at_distance_of_terminalParabolicCurvatureBoundProducer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.bounded_curvature_at_distance_of_terminalParabolicCurvatureBoundProducer ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.bounded_curvature_at_distance_of_terminalParabolicCurvatureBoundProducer

def TerminalParabolicRmBallBound {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (start ρ : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ i, ∀ t ∈ Set.Icc start 0, ∀ y : (X.term i).M,
    riemannianEDistOf (I := I3) ((X.term i).S.base.metric start) (X.term i).basepoint y ≤
      ENNReal.ofReal ρ →
    curvDerivNormSq (I := I3) 0 ((X.term i).S.base.metric t) y ≤ C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalParabolicRmBallBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalParabolicRmBallBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalParabolicRmBallBound ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalParabolicRmBallBound

def TerminalParabolicBallNesting {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (start rho ρ : ℝ) : Prop :=
  ∀ i, ∀ y : (X.term i).M,
    metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y ≤ rho →
      riemannianEDistOf (I := I3) ((X.term i).S.base.metric start) (X.term i).basepoint y ≤
        ENNReal.ofReal ρ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalParabolicBallNesting then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalParabolicBallNesting"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalParabolicBallNesting ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalParabolicBallNesting

theorem terminalParabolicCurvatureBound_iff_scale_windows
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (start : ℝ) :
    TerminalParabolicCurvatureBound X start ↔
      ∀ rho : ℝ, 0 < rho → ∃ ρ : ℝ, 0 < ρ ∧
        TerminalParabolicRmBallBound X start (2 * ρ) ∧
        TerminalParabolicBallNesting X start rho ρ := by
  constructor
  · intro h rho hrho
    obtain ⟨curvature, radius, hK, hR, hbound, hnest⟩ := h rho hrho
    refine ⟨radius / (2 * Real.sqrt curvature), by positivity, ?_, ?_⟩
    · refine ⟨curvature ^ 2, by positivity, fun i t ht y hy => ?_⟩
      have hne : Real.sqrt curvature ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hK)
      have hrad : 2 * (radius / (2 * Real.sqrt curvature)) = radius / Real.sqrt curvature := by
        field_simp
      rw [hrad] at hy
      exact hbound i t ht y hy
    · exact fun i y hy => hnest i y hy
  · intro h rho hrho
    obtain ⟨ρ, hρ, ⟨C, hC, hbound⟩, hnest⟩ := h rho hrho
    refine ⟨Real.sqrt C, 2 * ρ * Real.sqrt (Real.sqrt C),
      Real.sqrt_pos.mpr hC, by positivity, ?_, ?_⟩
    · intro i t ht y hy
      have hne : Real.sqrt (Real.sqrt C) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hC))
      have hrad : 2 * ρ * Real.sqrt (Real.sqrt C) / Real.sqrt (Real.sqrt C) = 2 * ρ := by
        field_simp
      rw [hrad] at hy
      simpa only [Real.sq_sqrt hC.le] using hbound i t ht y hy
    · intro i y hy
      have hne : Real.sqrt (Real.sqrt C) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hC))
      have hrad : 2 * ρ * Real.sqrt (Real.sqrt C) / (2 * Real.sqrt (Real.sqrt C)) = ρ := by
        field_simp
      rw [hrad]
      exact hnest i y hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalParabolicCurvatureBound_iff_scale_windows then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalParabolicCurvatureBound_iff_scale_windows"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalParabolicCurvatureBound_iff_scale_windows ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalParabolicCurvatureBound_iff_scale_windows

theorem terminalParabolicCurvatureBound_of_scale_windows
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (start : ℝ)
    (hrm : ∀ ρ : ℝ, 0 < ρ → TerminalParabolicRmBallBound X start ρ)
    (hnest : ∀ rho : ℝ, 0 < rho → ∃ ρ : ℝ, 0 < ρ ∧
      TerminalParabolicBallNesting X start rho ρ) :
    TerminalParabolicCurvatureBound X start :=
  (terminalParabolicCurvatureBound_iff_scale_windows X start).mpr fun rho hrho => by
    obtain ⟨ρ, hρ, hnest'⟩ := hnest rho hrho
    exact ⟨ρ, hρ, hrm (2 * ρ) (by positivity), hnest'⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalParabolicCurvatureBound_of_scale_windows then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalParabolicCurvatureBound_of_scale_windows"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalParabolicCurvatureBound_of_scale_windows ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalParabolicCurvatureBound_of_scale_windows

private theorem scalar_le_of_pointedFlowRmNormSqBounded {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (i : ℕ) {C : ℝ}
    (hC : PointedFlowRmNormSqBounded (X.term i) C) {t : ℝ}
    (ht : t ∈ (X.interval i).carrier) (y : (X.term i).M) :
    (X.term i).S.scalar t y ≤ (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt (_root_.Max.max C 0) := by
  have hrm : Tensor0SBundle.normSq0S (I := I3) ((X.term i).S.base.metric t) y 4
      (metricRm04At (I := I3) ((X.term i).S.base.metric t) y) ≤ _root_.Max.max C 0 :=
    le_trans (hC t ht y) (le_max_left _ _)
  have hscal := DifferentialGeometry.Geometry.Curvature.scalar_abs_le_rm
    (I := I3) ((X.term i).S.base.metric t) y
  have hdim : Module.finrank ℝ (TangentSpace I3 y) = Module.finrank ℝ ThreeSpace := rfl
  rw [hdim] at hscal
  exact le_trans (le_abs_self _) (le_trans hscal
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hrm) (by positivity)))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.scalar_le_of_pointedFlowRmNormSqBounded
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.scalar_le_of_pointedFlowRmNormSqBounded target :: scope.openDecls } }

private theorem exists_scalar_bound_at_zero {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (N : ℕ) :
    ∃ C : ℝ, ∀ i, i < N → ∀ y : (X.term i).M, (X.term i).S.scalar 0 y ≤ C := by
  induction N with
  | zero => exact ⟨0, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ N ih =>
    obtain ⟨C, hC⟩ := ih
    obtain ⟨C', hC'⟩ := X.source_bound N
    have h0 : (0 : ℝ) ∈ (X.interval N).carrier := by
      rw [X.carrier_eq N]
      exact ⟨by linarith [X.depth_pos N], le_rfl⟩
    refine ⟨max C ((Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt (_root_.Max.max C' 0)),
      fun i hi y => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
    · exact le_trans (hC i hlt y) (le_max_left _ _)
    · subst i
      exact le_trans (scalar_le_of_pointedFlowRmNormSqBounded X N hC' h0 y) (le_max_right _ _)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_scalar_bound_at_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_scalar_bound_at_zero target :: scope.openDecls } }

theorem boundedAtDistance_of_recentered_scalar_bound {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ A D : ℝ, 0 ≤ D → ∃ C : ℝ,
        ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ᶠ i in Filter.atTop,
          ∀ s ∈ Set.Icc (-(X.depth i / 2)) 0, ∀ z y : (X.term i).M,
            (X.term i).S.scalar s z ≤ A →
            metricDistance ((X.term i).S.base.metric s) z y ≤ D →
              (X.term i).S.scalar s y ≤ C) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, BoundedAtDistance X := by
  obtain ⟨e, he, hb⟩ := h
  refine ⟨e, he, ?_⟩
  intro eps hp hle X rho hrho
  obtain ⟨C, hC⟩ := hb eps hp hle 1 rho hrho.le
  have hmain : ∀ᶠ i in Filter.atTop, ∀ y : (X.term i).M,
      metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y ≤ rho →
        (X.term i).S.scalar 0 y ≤ C := by
    filter_upwards [hC X] with i hi y hy
    refine hi 0 ⟨by linarith [X.depth_pos i], le_rfl⟩ (X.term i).basepoint y ?_ hy
    rw [X.base_one i]
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hmain
  obtain ⟨Cexc, hCexc⟩ := exists_scalar_bound_at_zero X N
  refine ⟨max C Cexc, fun i y hy => ?_⟩
  by_cases hlt : i < N
  · exact le_trans (hCexc i hlt y) (le_max_right _ _)
  · exact le_trans (hN i (le_of_not_gt hlt) y hy) (le_max_left _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.boundedAtDistance_of_recentered_scalar_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.boundedAtDistance_of_recentered_scalar_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.boundedAtDistance_of_recentered_scalar_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.boundedAtDistance_of_recentered_scalar_bound

theorem bounded_curvature_at_distance {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hkappa : 0 < kappa) (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        BoundedAtDistance X ∧ TerminalDerivativeBounds X := by
  obtain ⟨epsBound, hepsBound, hbound⟩ := exists_boundedAtDistance.{u} hkappa
  obtain ⟨epsDeriv, hepsDeriv, hderiv⟩ := exists_terminalDerivativeBounds_of_boundedAtDistance.{u} hkappa
  refine ⟨min epsBound epsDeriv, lt_min hepsBound hepsDeriv, ?_⟩
  intro eps heps hle X
  have hb := hbound eps heps (hle.trans (min_le_left _ _)) sigma hsigma Phi hPhi X
  exact ⟨hb, hderiv eps heps (hle.trans (min_le_right _ _)) sigma hsigma Phi hPhi X hb⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.bounded_curvature_at_distance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.bounded_curvature_at_distance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.bounded_curvature_at_distance ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.bounded_curvature_at_distance

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
