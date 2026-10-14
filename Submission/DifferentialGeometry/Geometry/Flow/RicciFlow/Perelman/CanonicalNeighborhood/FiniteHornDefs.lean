import Submission.DifferentialGeometry.Geometry.Metric.ConeDistance
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import Mathlib.Topology.MetricSpace.Completion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open scoped _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W] [SigmaCompactSpace W]
structure EndRay (E : UniformSpace.Completion W) where
  length : ℝ
  length_pos : 0 < length
  point : ℝ → W
  radial : ∀ s ∈ Set.Ioc 0 length,
    _root_.Dist.dist (point s : UniformSpace.Completion W) E = s
  minimizing : ∀ s ∈ Set.Ioc 0 length, ∀ t ∈ Set.Ioc 0 length,
    _root_.Dist.dist (point s) (point t) = |s - t|

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndRay then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndRay"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndRay ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndRay

def EndRay.EventuallyEqual {E : UniformSpace.Completion W} (a b : EndRay E) : Prop :=
  ∃ d : ℝ, 0 < d ∧ d ≤ _root_.Min.min a.length b.length ∧
    ∀ s ∈ Set.Ioc 0 d, a.point s = b.point s

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndRay
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndRay.EventuallyEqual then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndRay.EventuallyEqual"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndRay.EventuallyEqual ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndRay.EventuallyEqual

structure GlobalNeckTube (W : Type u) [MetricSpace W] [ChartedSpace ThreeSpace W] where
  map : PartialDiffeomorph IC I3 Cylinder W ∞
  source_eq : map.source = Set.univ ×ˢ Set.Ioo (0 : ℝ) 1
  target_eq : map.target = Set.univ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckTube then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckTube"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckTube ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckTube

namespace GlobalNeckTube


def height (T : GlobalNeckTube W) (x : W) : ℝ := (T.map.symm x).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckTube.height then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckTube.height"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckTube.height ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckTube.height

omit [IsManifold I3 ∞ W] [SigmaCompactSpace W] in
theorem continuous_height (T : GlobalNeckTube W) : Continuous T.height := by
  have h : Continuous (T.map.symm : W → Cylinder) := by
    rw [← continuousOn_univ]
    change ContinuousOn T.map.invFun Set.univ
    simpa only [T.target_eq] using T.map.contMDiffOn_invFun.continuousOn
  exact continuous_snd.comp h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckTube.continuous_height then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckTube.continuous_height"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckTube.continuous_height ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckTube.continuous_height

omit [IsManifold I3 ∞ W] [SigmaCompactSpace W] in
theorem height_mem (T : GlobalNeckTube W) (x : W) : T.height x ∈ Set.Ioo (0 : ℝ) 1 := by
  have hx : x ∈ T.map.target := by rw [T.target_eq]; trivial
  have h := T.map.toPartialEquiv.map_target hx
  rw [T.source_eq] at h
  exact h.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckTube.height_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckTube.height_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckTube.height_mem ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckTube.height_mem


def sectionSet (T : GlobalNeckTube W) (q : ℝ) : Set W :=
  T.map '' (Set.univ ×ˢ ({q} : Set ℝ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckTube.sectionSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckTube.sectionSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckTube.sectionSet ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckTube.sectionSet

omit [IsManifold I3 ∞ W] [SigmaCompactSpace W] in
theorem mem_sectionSet_iff (T : GlobalNeckTube W) {q : ℝ} (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (x : W) : x ∈ T.sectionSet q ↔ T.height x = q := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hyq : y.2 = q := hy.2
    have hys : y ∈ T.map.source := by
      rw [T.source_eq]
      exact ⟨Set.mem_univ _, hyq.symm ▸ hq⟩
    change (T.map.invFun (T.map y)).2 = q
    rw [T.map.left_inv' hys]
    exact hyq
  · intro hx
    refine ⟨T.map.symm x, ⟨Set.mem_univ _, hx⟩, ?_⟩
    exact T.map.right_inv' (by rw [T.target_eq]; trivial)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckTube.mem_sectionSet_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckTube.mem_sectionSet_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckTube.mem_sectionSet_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckTube.mem_sectionSet_iff

omit [IsManifold I3 ∞ W] [SigmaCompactSpace W] in
theorem isCompact_slab (T : GlobalNeckTube W) {a b : ℝ} (ha : 0 < a) (hb : b < 1) :
    IsCompact (T.map '' (Set.univ ×ˢ Set.Icc a b)) := by
  apply ((isCompact_univ : IsCompact (Set.univ : Set (Sphere 2))).prod _root_.CompactIccSpace.isCompact_Icc).image_of_continuousOn
  apply T.map.contMDiffOn_toFun.continuousOn.mono
  intro x hx
  rw [T.source_eq]
  exact ⟨Set.mem_univ _, ha.trans_le hx.2.1, hx.2.2.trans_lt hb⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckTube.isCompact_slab then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckTube.isCompact_slab"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckTube.isCompact_slab ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckTube.isCompact_slab

omit [IsManifold I3 ∞ W] [SigmaCompactSpace W] in
theorem path_meets_section (T : GlobalNeckTube W) {q : ℝ}
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) (c : ℝ → W)
    (hc : ContinuousOn c (Set.Icc (0 : ℝ) 1))
    (hstart : T.height (c 0) < q) (hend : q < T.height (c 1)) :
    ∃ s ∈ Set.Icc (0 : ℝ) 1, c s ∈ T.sectionSet q := by
  have hh : ContinuousOn (T.height ∘ c) (Set.Icc (0 : ℝ) 1) :=
    T.continuous_height.comp_continuousOn hc
  obtain ⟨s, hs, hsq⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hh
    ⟨hstart.le, hend.le⟩
  exact ⟨s, hs, (T.mem_sectionSet_iff hq (c s)).2 hsq⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckTube.path_meets_section then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckTube.path_meets_section"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckTube.path_meets_section ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckTube.path_meets_section

omit [IsManifold I3 ∞ W] [SigmaCompactSpace W] in
theorem range_sectionMap (T : GlobalNeckTube W) (q : ℝ) :
    Set.range (fun p : Sphere 2 => T.map (p, q)) = T.sectionSet q := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨(p, q), ⟨Set.mem_univ _, rfl⟩, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.1, ?_⟩
    rw [← hy.2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckTube.range_sectionMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckTube.range_sectionMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckTube.range_sectionMap ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckTube.range_sectionMap

end GlobalNeckTube

structure GlobalNeckCrossSection
    (F : PartialDiffeomorph IC I3 Cylinder W ∞) (subend : ℕ → Set W)
    (axis : ℝ → W) (axisLength : ℝ) where
  tube : GlobalNeckTube W
  center_eq : ∀ p : Sphere 2, tube.map (p, 1 / 2) = F (p, 0)
  deep_side : ∃ i, ∀ x ∈ subend i, tube.height x < 1 / 2
  crossing_parameter : ℝ
  crossing_mem : crossing_parameter ∈ Set.Ioc 0 axisLength
  axis_crosses : ∃ p : Sphere 2, F (p, 0) = axis crossing_parameter

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckCrossSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckCrossSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckCrossSection ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckCrossSection

omit [IsManifold I3 ∞ W] [SigmaCompactSpace W] in
theorem GlobalNeckCrossSection.path_meets_center
    {F : PartialDiffeomorph IC I3 Cylinder W ∞} {subend : ℕ → Set W}
    {axis : ℝ → W} {axisLength : ℝ}
    (G : GlobalNeckCrossSection F subend axis axisLength) (c : ℝ → W)
    (hc : ContinuousOn c (Set.Icc (0 : ℝ) 1))
    (hstart : G.tube.height (c 0) < 1 / 2) (hend : 1 / 2 < G.tube.height (c 1)) :
    ∃ s ∈ Set.Icc (0 : ℝ) 1, c s ∈ Set.range (fun p : Sphere 2 => F (p, 0)) := by
  obtain ⟨s, hs, y, hy, heq⟩ := G.tube.path_meets_section
    (by norm_num : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1) c hc hstart hend
  have hyq : y.2 = 1 / 2 := hy.2
  refine ⟨s, hs, y.1, ?_⟩
  change F (y.1, 0) = c s
  rw [← G.center_eq, ← hyq]
  exact heq

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckCrossSection
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckCrossSection.path_meets_center then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckCrossSection.path_meets_center"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckCrossSection.path_meets_center ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.GlobalNeckCrossSection.path_meets_center

structure _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
    (g : SmoothRiemannianMetric I3 W) where
  intrinsic : ∀ x y : W, _root_.Dist.dist x y = metricDistance g x y
  endpoint : UniformSpace.Completion W
  endpoint_missing : ∀ x : W, (x : UniformSpace.Completion W) ≠ endpoint
  axial : EndRay endpoint
  tube : GlobalNeckTube W
  subend : ℕ → Set W
  cut_height : ℕ → ℝ
  cut_height_mem : ∀ i, cut_height i ∈ Set.Ioo (0 : ℝ) 1
  cut_height_zero : Filter.Tendsto cut_height Filter.atTop (nhds 0)
  subend_eq : ∀ i, subend i = {x | tube.height x < cut_height i}
  open_subend : ∀ i, IsOpen (subend i)
  connected_subend : ∀ i, IsConnected (subend i)
  nested : ∀ i, subend (i + 1) ⊆ subend i
  cofinal_axial : ∀ i, ∃ d : ℝ, 0 < d ∧ d ≤ axial.length ∧
    ∀ s ∈ Set.Ioc 0 d, axial.point s ∈ subend i
  ambient : Type u
  [ambient_metric : MetricSpace ambient]
  [ambient_complete : CompleteSpace ambient]
  inclusion : W → ambient
  inclusion_continuous : Continuous inclusion
  inclusion_injective : Function.Injective inclusion
  ambient_end : ambient
  ambient_axial : ∀ s ∈ Set.Ioc 0 axial.length, _root_.Dist.dist (inclusion (axial.point s)) ambient_end = s
  local_distance : ∀ x : W, ∃ U ∈ nhds x, ∀ y ∈ U, ∀ z ∈ U,
    _root_.Dist.dist (inclusion y) (inclusion z) = _root_.Dist.dist y z
  outer_frontier : Set ambient
  frontier_eq : outer_frontier = frontier (Set.range inclusion) \ {ambient_end}
  inclusion_isOpenEmbedding : Topology.IsOpenEmbedding inclusion
  frontier_far : ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ outer_frontier, δ ≤ _root_.Dist.dist z ambient_end
  deep_capture : ∃ δ : ℝ, 0 < δ ∧ ∀ z : ambient, z ≠ ambient_end →
    _root_.Dist.dist z ambient_end < δ → z ∈ Set.range inclusion
  nonnegative : SecLower g 0 Set.univ
  curvature_diverges : ∀ C : ℝ, ∃ i, ∀ x ∈ subend i, C < metricScalarAt g x
  curvature_distance_lower : ∃ c : ℝ, 0 < c ∧ ∀ x ∈ subend 0,
    c ≤ metricScalarAt g x * _root_.Dist.dist (x : UniformSpace.Completion W) endpoint ^ 2
  neck_precision : ℝ
  neck_precision_pos : 0 < neck_precision
  neck_precision_small : neck_precision < 1 / 11
  collar_depth : ℝ
  collar_depth_pos : 0 < collar_depth
  cylindrical_tail : ∃ i,
    ∀ x ∈ subend i, ∃ (cyl : CylinderReference)
      (F : PartialDiffeomorph IC I3 Cylinder W ∞) (p : Sphere 2),
      F (p, 0) = x ∧
      Nonempty (GlobalNeckCrossSection F subend axial.point axial.length) ∧
      Set.univ ×ˢ Set.Icc (-collar_depth) collar_depth ⊆ F.source ∧
      ∃ hQ : 0 < metricScalarAt g x,
        Nonempty (MetricComparisonOn (fun _ => cyl.metric 0)
          (fun _ => scaleMetric (metricScalarAt g x) hQ g) F
          (Set.univ ×ˢ Set.Icc (-collar_depth) collar_depth)
          {0} (⌈neck_precision⁻¹⌉₊) neck_precision)
  ambient_end_isometry : ∃ i, (∀ x ∈ subend i, ∀ y ∈ subend i,
      _root_.Dist.dist x y = _root_.Dist.dist (inclusion x) (inclusion y)) ∧
    ∀ x ∈ subend i, _root_.Dist.dist (x : UniformSpace.Completion W) endpoint =
      _root_.Dist.dist (inclusion x) ambient_end

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

attribute [local instance] FiniteHorn.ambient_metric

structure EndGeometry {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g) where
  unique_endpoint : (⋂ i, closure ((fun x : W => (x : UniformSpace.Completion W)) '' H.subend i)) =
    {H.endpoint}
  intrinsic_ambient : ∃ i, (∀ x ∈ H.subend i, ∀ y ∈ H.subend i,
    _root_.Dist.dist x y = _root_.Dist.dist (H.inclusion x) (H.inclusion y)) ∧
    ∀ x ∈ H.subend i, _root_.Dist.dist (x : UniformSpace.Completion W) H.endpoint =
      _root_.Dist.dist (H.inclusion x) H.ambient_end
  rays : ∃ i, ∀ x ∈ H.subend i, ∃ a : EndRay H.endpoint, a.point a.length = x
  frontier_escape : ∀ w : ℕ → W,
    Filter.Tendsto (fun i => (w i : UniformSpace.Completion W)) Filter.atTop (nhds H.endpoint) →
    ∀ R : ℝ, 0 < R → ∀ᶠ i in Filter.atTop, ∀ z ∈ H.outer_frontier,
      R * _root_.Dist.dist (w i : UniformSpace.Completion W) H.endpoint < _root_.Dist.dist (H.inclusion (w i)) z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndGeometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndGeometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndGeometry ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndGeometry

structure RayApproximation {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g)
    (a b : EndRay H.endpoint) (lo hi : Fin 2 → ℝ) where
  target_index : ℕ
  arm_index : ℕ
  connector_index : ℕ
  target_buffer : closure (H.subend target_index) ⊆ H.subend arm_index
  arm_buffer : closure (H.subend arm_index) ⊆ H.subend connector_index
  target_mem : (∀ s ∈ Set.Icc (lo 0) (hi 0), a.point s ∈ H.subend target_index) ∧
    (∀ t ∈ Set.Icc (lo 1) (hi 1), b.point t ∈ H.subend target_index)
  base : ℕ → W
  arm : Fin 2 → ℕ → ℝ → W
  length : Fin 2 → ℕ → ℝ
  length_pos : ∀ k i, 0 < length k i
  arm_smooth : ∀ k i, ContMDiffOn 𝓘(ℝ, ℝ) I3 ∞ (arm k i) (Set.Icc 0 (length k i))
  arm_mem : ∀ k i s, s ∈ Set.Icc 0 (length k i) → arm k i s ∈ H.subend arm_index
  parameter : Fin 2 → ℕ → ℝ → ℝ
  starts : ∀ k i, arm k i 0 = base i
  minimizing : ∀ k i s, s ∈ Set.Icc 0 (length k i) → ∀ t ∈ Set.Icc 0 (length k i),
    _root_.Dist.dist (arm k i s) (arm k i t) = |s - t|
  parameter_mono : ∀ k i, MonotoneOn (parameter k i) (Set.Icc (lo k) (hi k))
  parameter_mem : ∀ k i s, s ∈ Set.Icc (lo k) (hi k) → parameter k i s ∈ Set.Icc 0 (length k i)
  connectors : ∀ i, ∀ s ∈ Set.Icc 0 (length 0 i), ∀ t ∈ Set.Icc 0 (length 1 i),
    ∃ c : ℝ → W, c 0 = arm 0 i s ∧
      c 1 = arm 1 i t ∧
      ContMDiffOn 𝓘(ℝ, ℝ) I3 ∞ c (Set.Icc (0 : ℝ) 1) ∧
      (∀ u ∈ Set.Icc (0 : ℝ) 1, c u ∈ H.subend connector_index) ∧
      ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ v ∈ Set.Icc (0 : ℝ) 1,
        _root_.Dist.dist (c u) (c v) = |u - v| *
          _root_.Dist.dist (arm 0 i s) (arm 1 i t)
  uniform : ∀ eta : ℝ, 0 < eta → ∀ᶠ i in Filter.atTop,
    _root_.Dist.dist (base i : UniformSpace.Completion W) H.endpoint < eta ∧
    ∀ s ∈ Set.Icc (lo 0) (hi 0), ∀ t ∈ Set.Icc (lo 1) (hi 1),
      |parameter 0 i s - s| < eta ∧ |parameter 1 i t - t| < eta ∧
      _root_.Dist.dist (arm 0 i (parameter 0 i s)) (a.point s) < eta ∧
      _root_.Dist.dist (arm 1 i (parameter 1 i t)) (b.point t) < eta ∧
      |dist (arm 0 i (parameter 0 i s)) (arm 1 i (parameter 1 i t)) -
        _root_.Dist.dist (a.point s) (b.point t)| < eta

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.RayApproximation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.RayApproximation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.RayApproximation ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.RayApproximation

def endComparisonAngle {E : UniformSpace.Completion W} (a b : EndRay E) (s t : ℝ) : ℝ :=
  Real.arccos ((s ^ 2 + t ^ 2 - _root_.Dist.dist (a.point s) (b.point t) ^ 2) / (2 * s * t))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endComparisonAngle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endComparisonAngle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endComparisonAngle ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endComparisonAngle

structure EndAngles {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g) where
  angle : EndRay H.endpoint → EndRay H.endpoint → ℝ
  range : ∀ a b, angle a b ∈ Set.Icc 0 Real.pi
  limit : ∀ a b, ∀ eta : ℝ, 0 < eta → ∃ d : ℝ, 0 < d ∧ d ≤ _root_.Min.min a.length b.length ∧
    ∀ s ∈ Set.Ioc 0 d, ∀ t ∈ Set.Ioc 0 d, |endComparisonAngle a b s t - angle a b| < eta
  monotone : ∀ a b : EndRay H.endpoint, ∃ d : ℝ, 0 < d ∧ d ≤ _root_.Min.min a.length b.length ∧
    ∀ s s' t t', 0 < s → s ≤ s' → s' ≤ d → 0 < t → t ≤ t' → t' ≤ d →
      endComparisonAngle a b s' t' ≤ endComparisonAngle a b s t
  self : ∀ a, angle a a = 0
  symm : ∀ a b, angle a b = angle b a
  triangle : ∀ a b c, angle a c ≤ angle a b + angle b c
  quotient : Type u
  [metric : MetricSpace quotient]
  classOf : EndRay H.endpoint → quotient
  onto : Function.Surjective classOf
  distance : ∀ a b, _root_.Dist.dist (classOf a) (classOf b) = angle a b
  eventual_eq : ∀ a b, a.EventuallyEqual b → classOf a = classOf b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndAngles then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndAngles"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndAngles ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndAngles

attribute [local instance] EndAngles.metric


structure AnnularConvergence {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g)
    (angles : EndAngles H) (ray : EndRay H.endpoint) (d : ℕ → ℝ) where
  relation : ℝ → ℝ → ℕ → Set ((ℝ × UniformSpace.Completion angles.quotient) × W)
  error : ℝ → ℝ → ℕ → ℝ
  error_pos : ∀ a b i, 0 < error a b i
  error_zero : ∀ a b, 0 < a → a < b → Filter.Tendsto (error a b) Filter.atTop (nhds 0)
  annuli : ∀ a b, 0 < a → a < b → ∀ᶠ i in Filter.atTop,
    IsCompact {w : W | a ≤ _root_.Dist.dist (w : UniformSpace.Completion W) H.endpoint / d i ∧
      _root_.Dist.dist (w : UniformSpace.Completion W) H.endpoint / d i ≤ b} ∧
    (∀ x w, (x, w) ∈ relation a b i → x.1 ∈ Set.Icc a b ∧
      _root_.Dist.dist (w : UniformSpace.Completion W) H.endpoint / d i ∈ Set.Icc a b) ∧
    (∀ x : ℝ × UniformSpace.Completion angles.quotient, x.1 ∈ Set.Icc a b →
      ∃ y w, (y, w) ∈ relation a b i ∧ Metric.coneDistance x y < error a b i) ∧
    (∀ w : W, _root_.Dist.dist (w : UniformSpace.Completion W) H.endpoint / d i ∈ Set.Icc a b →
      ∃ x z, (x, z) ∈ relation a b i ∧ _root_.Dist.dist w z / d i < error a b i) ∧
    (∀ x w y z, (x, w) ∈ relation a b i → (y, z) ∈ relation a b i →
      |Metric.coneDistance x y - _root_.Dist.dist w z / d i| < error a b i) ∧
    (∀ x w, (x, w) ∈ relation a b i →
      |x.1 - _root_.Dist.dist (w : UniformSpace.Completion W) H.endpoint / d i| < error a b i) ∧
    (a < 1 → 1 < b →
      (((1, (angles.classOf ray : UniformSpace.Completion angles.quotient)), ray.point (d i))) ∈
        relation a b i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.AnnularConvergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.AnnularConvergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.AnnularConvergence ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.AnnularConvergence


structure HornBarriers {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g)
    (ray : EndRay H.endpoint) (d : ℕ → ℝ) where
  sphere : ℕ → Sphere 2 → W
  embedding : ∀ i, _root_.Topology.IsEmbedding (sphere i)
  smooth : ∀ i, ContMDiff I2 I3 ∞ (sphere i)
  diameter_bound : ∃ L : ℝ, 0 < L ∧ ∀ᶠ i in Filter.atTop, ∀ x ∈ Set.range (sphere i),
    _root_.Dist.dist (ray.point (d i)) x ≤ L / Real.sqrt (metricScalarAt g (ray.point (d i)))
  radial_barrier : ∀ eta : ℝ, 0 < eta → eta < 1 / 10 → ∀ᶠ i in Filter.atTop,
    ∀ c : C(Set.Icc (0 : ℝ) 1, W),
      _root_.Dist.dist (c ⟨0, by simp⟩ : UniformSpace.Completion W) H.endpoint / d i < 1 - eta →
      1 + eta < _root_.Dist.dist (c ⟨1, by simp⟩ : UniformSpace.Completion W) H.endpoint / d i →
      ∃ t, c t ∈ Set.range (sphere i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.HornBarriers then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.HornBarriers"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.HornBarriers ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.HornBarriers

structure NeckSectionBarrier {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g)
    (ray : EndRay H.endpoint) (d : ℕ → ℝ) where
  tube : ℕ → GlobalNeckTube W
  section_diameter : ∃ L : ℝ, 0 < L ∧ ∀ᶠ i in Filter.atTop,
    ∀ x ∈ (tube i).sectionSet (1 / 2),
      _root_.Dist.dist (ray.point (d i)) x ≤ L / Real.sqrt (metricScalarAt g (ray.point (d i)))
  separates : ∀ eta : ℝ, 0 < eta → eta < 1 / 10 → ∀ᶠ i in Filter.atTop,
    ∀ c : C(Set.Icc (0 : ℝ) 1, W),
      _root_.Dist.dist (c ⟨0, by simp⟩ : UniformSpace.Completion W) H.endpoint / d i < 1 - eta →
      1 + eta < _root_.Dist.dist (c ⟨1, by simp⟩ : UniformSpace.Completion W) H.endpoint / d i →
      ∃ t, c t ∈ (tube i).sectionSet (1 / 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.NeckSectionBarrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.NeckSectionBarrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.NeckSectionBarrier ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.NeckSectionBarrier


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
