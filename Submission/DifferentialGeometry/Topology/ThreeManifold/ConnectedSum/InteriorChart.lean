import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Collar

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.Manifold _root_.ContDiff _root_.Topology

noncomputable section

attribute [local instance] Classical.propDecidable

namespace DifferentialGeometry.Topology

namespace ConnectedSumQuotient

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : Type*} [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace K N]
  {n : ℕ}

variable (c : BallChart n I M) (d : BallChart n J N)
  (a : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ≃ₜ
    Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)

section DefaultPoint

variable (hn : 0 < n)

def spherePoint : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  ⟨EuclideanSpace.single ⟨0, hn⟩ 1, by simp⟩

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.spherePoint with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.spherePoint"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.spherePoint ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.spherePoint

theorem norm_spherePoint : ‖(spherePoint hn : EuclideanSpace ℝ (Fin n))‖ = 1 := by
  simp [spherePoint]

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.norm_spherePoint with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.norm_spherePoint"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.norm_spherePoint ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.norm_spherePoint

def leftDefault : c.Punctured :=
  c.radialMap (spherePoint hn) (3 / 2) ⟨by norm_num, by norm_num⟩

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.leftDefault with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.leftDefault"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.leftDefault ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.leftDefault

def rightDefault : d.Punctured :=
  d.radialMap (spherePoint hn) (3 / 2) ⟨by norm_num, by norm_num⟩

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.rightDefault with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.rightDefault"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.rightDefault ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.rightDefault

theorem leftDefault_val :
    (leftDefault c hn : M) = c.chart ((3 / 2 : ℝ) • (spherePoint hn : EuclideanSpace ℝ (Fin n))) :=
  BallChart.radialMap_val c (spherePoint hn) (3 / 2) _

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.leftDefault_val with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.leftDefault_val"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.leftDefault_val ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.leftDefault_val

theorem leftDefault_mem_interior [T2Space M] : (leftDefault c hn : M) ∈ (c.interior : Set M) := by
  change (leftDefault c hn : M) ∉ c.chart '' Metric.closedBall 0 1
  rw [leftDefault_val]
  rintro ⟨y, hy, heq⟩
  have hy1 : ‖y‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hy
  have hsource : (3 / 2 : ℝ) • (spherePoint hn : EuclideanSpace ℝ (Fin n)) ∈ c.chart.source :=
    c.closedBall_subset_source (by
      rw [Metric.mem_closedBall, dist_zero_right,
        BallChart.norm_radial (spherePoint hn) (by norm_num)]
      norm_num)
  have hyz : y = (3 / 2 : ℝ) • (spherePoint hn : EuclideanSpace ℝ (Fin n)) :=
    c.chart.toPartialEquiv.injOn (c.closedBall_one_subset_source hy) hsource heq
  have hnorm : ‖y‖ = 3 / 2 := by
    rw [hyz, BallChart.norm_radial (spherePoint hn) (by norm_num)]
  linarith

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.leftDefault_mem_interior with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.leftDefault_mem_interior"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.leftDefault_mem_interior ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.leftDefault_mem_interior

end DefaultPoint

section Left

variable [T2Space M]

def leftRegion (f : OpenPartialHomeomorph M H) : Set c.Punctured :=
  Subtype.val ⁻¹' (f.source ∩ (c.interior : Set M))

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.leftRegion with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.leftRegion"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.leftRegion ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.leftRegion

@[simp]
theorem mem_leftRegion (f : OpenPartialHomeomorph M H) (p : c.Punctured) :
    p ∈ leftRegion c f ↔ (p : M) ∈ f.source ∧ (p : M) ∈ (c.interior : Set M) :=
  Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.mem_leftRegion with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.mem_leftRegion"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.mem_leftRegion ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.mem_leftRegion

theorem isOpen_leftRegion (f : OpenPartialHomeomorph M H) : IsOpen (leftRegion c f) :=
  (f.open_source.inter c.interior.isOpen).preimage continuous_subtype_val

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.isOpen_leftRegion with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.isOpen_leftRegion"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.isOpen_leftRegion ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.isOpen_leftRegion

theorem leftRegion_disjoint_seam (f : OpenPartialHomeomorph M H) :
    ∀ z, c.boundaryMap z ∉ leftRegion c f := by
  intro z hp
  have hmem : (c.boundaryMap z : M) ∈ c.chart '' Metric.closedBall 0 1 :=
    ⟨(z : EuclideanSpace ℝ (Fin n)),
      by simp [Metric.mem_closedBall],
      rfl⟩
  exact (BallChart.mem_interior (c := c)).mp hp.2 hmem

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.leftRegion_disjoint_seam with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.leftRegion_disjoint_seam"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.leftRegion_disjoint_seam ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.leftRegion_disjoint_seam

def leftTarget (f : OpenPartialHomeomorph M H) : Set (ConnectedSumQuotient c d a) :=
  inl c d a '' leftRegion c f

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.leftTarget with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.leftTarget"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.leftTarget ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.leftTarget

theorem mem_leftTarget (f : OpenPartialHomeomorph M H) (x : ConnectedSumQuotient c d a) :
    x ∈ leftTarget c d a f ↔ ∃ p : c.Punctured, p ∈ leftRegion c f ∧ inl c d a p = x :=
  Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.mem_leftTarget with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.mem_leftTarget"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.mem_leftTarget ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.mem_leftTarget

theorem isOpen_leftTarget (f : OpenPartialHomeomorph M H) : IsOpen (leftTarget c d a f) :=
  isOpen_image_inl c d a (isOpen_leftRegion c f) (leftRegion_disjoint_seam c f)

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.isOpen_leftTarget with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.isOpen_leftTarget"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.isOpen_leftTarget ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.isOpen_leftTarget

def leftChartSource (f : OpenPartialHomeomorph M H) : Set H :=
  f '' (f.source ∩ (c.interior : Set M))

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.leftChartSource with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.leftChartSource"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.leftChartSource ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.leftChartSource

theorem mem_leftChartSource (f : OpenPartialHomeomorph M H) (y : H) :
    y ∈ leftChartSource c f ↔ y ∈ f.target ∧ f.symm y ∈ (c.interior : Set M) := by
  constructor
  · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
    refine ⟨f.map_source hx1, ?_⟩
    rwa [f.left_inv hx1]
  · rintro ⟨hy, hys⟩
    exact ⟨f.symm y, ⟨f.map_target hy, hys⟩, f.right_inv hy⟩

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.mem_leftChartSource with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.mem_leftChartSource"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.mem_leftChartSource ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.mem_leftChartSource

theorem isOpen_leftChartSource (f : OpenPartialHomeomorph M H) :
    IsOpen (leftChartSource c f) :=
  f.isOpen_image_of_subset_source (f.open_source.inter c.interior.isOpen) Set.inter_subset_left

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.isOpen_leftChartSource with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.isOpen_leftChartSource"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.isOpen_leftChartSource ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.isOpen_leftChartSource

theorem leftChartSource_subset_target (f : OpenPartialHomeomorph M H) :
    leftChartSource c f ⊆ f.target :=
  fun _ hy => ((mem_leftChartSource c f _).mp hy).1

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.leftChartSource_subset_target with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.leftChartSource_subset_target"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.leftChartSource_subset_target ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.leftChartSource_subset_target

theorem symm_mem_of_mem_leftChartSource (f : OpenPartialHomeomorph M H) (y : H)
    (hy : y ∈ leftChartSource c f) :
    f.symm y ∈ f.source ∩ (c.interior : Set M) := by
  obtain ⟨x, ⟨hx1, hx2⟩, hxy⟩ := hy
  rw [← hxy, f.left_inv hx1]
  exact ⟨hx1, hx2⟩

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.symm_mem_of_mem_leftChartSource with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.symm_mem_of_mem_leftChartSource"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.symm_mem_of_mem_leftChartSource ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.symm_mem_of_mem_leftChartSource

def leftCoord (hn : 0 < n) (f : OpenPartialHomeomorph M H) (y : H) : c.Punctured :=
  if h : y ∈ leftChartSource c f then
    ⟨f.symm y, fun hmem =>
      (BallChart.mem_interior (c := c)).mp (symm_mem_of_mem_leftChartSource c f y h).2
        (Set.image_mono Metric.ball_subset_closedBall hmem)⟩
  else leftDefault c hn

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.leftCoord with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.leftCoord"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.leftCoord ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.leftCoord

theorem leftCoord_val_of_mem (hn : 0 < n) (f : OpenPartialHomeomorph M H) (y : H)
    (hy : y ∈ leftChartSource c f) : (leftCoord c hn f y : M) = f.symm y := by
  rw [leftCoord, dif_pos hy]

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.leftCoord_val_of_mem with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.leftCoord_val_of_mem"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.leftCoord_val_of_mem ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.leftCoord_val_of_mem

theorem leftCoord_mem_leftRegion (hn : 0 < n) (f : OpenPartialHomeomorph M H) (y : H)
    (hy : y ∈ leftChartSource c f) : leftCoord c hn f y ∈ leftRegion c f := by
  rw [mem_leftRegion]
  obtain ⟨h1, h2⟩ := symm_mem_of_mem_leftChartSource c f y hy
  exact ⟨by rw [leftCoord_val_of_mem c hn f y hy]; exact h1,
    by rw [leftCoord_val_of_mem c hn f y hy]; exact h2⟩

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.leftCoord_mem_leftRegion with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.leftCoord_mem_leftRegion"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.leftCoord_mem_leftRegion ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.leftCoord_mem_leftRegion

def leftToFun (hn : 0 < n) (f : OpenPartialHomeomorph M H) :
    H → ConnectedSumQuotient c d a :=
  fun y => inl c d a (leftCoord c hn f y)

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.leftToFun with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.leftToFun"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.leftToFun ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.leftToFun

def leftSubtypeMap (f : OpenPartialHomeomorph M H) :
    ↥(leftChartSource c f) → c.Punctured :=
  fun y => ⟨f.symm (y : H), fun hmem =>
    (BallChart.mem_interior (c := c)).mp
      (symm_mem_of_mem_leftChartSource c f (y : H) y.2).2
      (Set.image_mono Metric.ball_subset_closedBall hmem)⟩

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.leftSubtypeMap with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.leftSubtypeMap"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.leftSubtypeMap ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.leftSubtypeMap

theorem leftSubtypeMap_val (f : OpenPartialHomeomorph M H) (y : ↥(leftChartSource c f)) :
    (leftSubtypeMap c f y : M) = f.symm (y : H) := rfl

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.leftSubtypeMap_val with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.leftSubtypeMap_val"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.leftSubtypeMap_val ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.leftSubtypeMap_val

theorem leftCoord_eq_leftSubtypeMap (hn : 0 < n) (f : OpenPartialHomeomorph M H)
    (y : ↥(leftChartSource c f)) :
    leftCoord c hn f (y : H) = leftSubtypeMap c f y :=
  Subtype.ext (leftCoord_val_of_mem c hn f (y : H) y.2)

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.leftCoord_eq_leftSubtypeMap with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.leftCoord_eq_leftSubtypeMap"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.leftCoord_eq_leftSubtypeMap ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.leftCoord_eq_leftSubtypeMap

theorem leftToFun_comp_subtype_val (hn : 0 < n) (f : OpenPartialHomeomorph M H) :
    leftToFun c d a hn f ∘ (Subtype.val : ↥(leftChartSource c f) → H) =
      inl c d a ∘ leftSubtypeMap c f := by
  funext y
  exact congrArg (inl c d a) (leftCoord_eq_leftSubtypeMap c hn f y)

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.leftToFun_comp_subtype_val with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.leftToFun_comp_subtype_val"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.leftToFun_comp_subtype_val ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.leftToFun_comp_subtype_val

theorem leftSubtypeMap_continuous (f : OpenPartialHomeomorph M H) :
    Continuous (leftSubtypeMap c f) := by
  have hbase : Continuous fun y : ↥(leftChartSource c f) => f.symm (y : H) :=
    f.continuousOn_symm.comp_continuous continuous_subtype_val
      (fun y => leftChartSource_subset_target c f y.2)
  exact hbase.subtype_mk _

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.leftSubtypeMap_continuous with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.leftSubtypeMap_continuous"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.leftSubtypeMap_continuous ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.leftSubtypeMap_continuous

theorem leftToFun_continuousOn (hn : 0 < n) (f : OpenPartialHomeomorph M H) :
    ContinuousOn (leftToFun c d a hn f) (leftChartSource c f) := by
  rw [continuousOn_iff_continuous_domRestrict]
  refine ((continuous_inl c d a).comp (leftSubtypeMap_continuous c f)).congr fun y => ?_
  exact congrArg (inl c d a) (leftCoord_eq_leftSubtypeMap c hn f y).symm

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.leftToFun_continuousOn with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.leftToFun_continuousOn"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.leftToFun_continuousOn ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.leftToFun_continuousOn

theorem leftSubtypeMap_image_subset (f : OpenPartialHomeomorph M H)
    (V : Set ↥(leftChartSource c f)) : leftSubtypeMap c f '' V ⊆ leftRegion c f := by
  rintro p ⟨y, -, rfl⟩
  rw [mem_leftRegion]
  exact symm_mem_of_mem_leftChartSource c f (y : H) y.2

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.leftSubtypeMap_image_subset with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.leftSubtypeMap_image_subset"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.leftSubtypeMap_image_subset ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.leftSubtypeMap_image_subset

theorem isOpen_leftSubtypeMap_image (f : OpenPartialHomeomorph M H)
    {V : Set ↥(leftChartSource c f)} (hV : IsOpen V) :
    IsOpen (leftSubtypeMap c f '' V) := by
  have hVopen : IsOpen ((Subtype.val : ↥(leftChartSource c f) → H) '' V) :=
    (isOpen_leftChartSource c f).isOpenEmbedding_subtypeVal.isOpenMap V hV
  have hW : IsOpen (f.symm '' ((Subtype.val : ↥(leftChartSource c f) → H) '' V)) :=
    f.isOpen_image_symm_of_subset_target hVopen (by
      rintro z ⟨y, -, rfl⟩
      exact leftChartSource_subset_target c f y.2)
  have heq : leftSubtypeMap c f '' V =
      Subtype.val ⁻¹' (f.symm '' ((Subtype.val : ↥(leftChartSource c f) → H) '' V)) := by
    ext p
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(y : H), ⟨y, hy, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨y, hy, rfl⟩, hzy⟩
      exact ⟨y, hy, Subtype.ext hzy⟩
  rw [heq]
  exact hW.preimage continuous_subtype_val

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.isOpen_leftSubtypeMap_image with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.isOpen_leftSubtypeMap_image"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.isOpen_leftSubtypeMap_image ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.isOpen_leftSubtypeMap_image

theorem leftToFun_openMap (hn : 0 < n) (f : OpenPartialHomeomorph M H) :
    IsOpenMap ((leftChartSource c f).domRestrict (leftToFun c d a hn f)) := by
  intro V hV
  have himg : (leftChartSource c f).domRestrict (leftToFun c d a hn f) '' V =
      leftToFun c d a hn f '' ((Subtype.val : ↥(leftChartSource c f) → H) '' V) := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact ⟨(y : H), ⟨y, hy, rfl⟩, hxy⟩
    · rintro ⟨y, ⟨y', hy', hyy'⟩, hxy⟩
      refine ⟨y', hy', ?_⟩
      change leftToFun c d a hn f (y' : H) = x
      rw [hyy']
      exact hxy
  rw [himg]
  rw [← Set.image_comp, leftToFun_comp_subtype_val c d a hn f, Set.image_comp]
  refine isOpen_image_inl c d a (isOpen_leftSubtypeMap_image c f hV) ?_
  exact fun z hz => leftRegion_disjoint_seam c f z (leftSubtypeMap_image_subset c f V hz)

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.leftToFun_openMap with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.leftToFun_openMap"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.leftToFun_openMap ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.leftToFun_openMap

theorem leftTargetExists (f : OpenPartialHomeomorph M H) (x : ConnectedSumQuotient c d a)
    (hx : x ∈ leftTarget c d a f) :
    ∃ p : c.Punctured, p ∈ leftRegion c f ∧ inl c d a p = x :=
  (mem_leftTarget c d a f x).mp hx

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.leftTargetExists with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.leftTargetExists"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.leftTargetExists ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.leftTargetExists

def leftWitness (f : OpenPartialHomeomorph M H) (x : ConnectedSumQuotient c d a)
    (hx : x ∈ leftTarget c d a f) : c.Punctured :=
  Classical.choose (leftTargetExists c d a f x hx)

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.leftWitness with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.leftWitness"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.leftWitness ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.leftWitness

theorem leftWitness_mem (f : OpenPartialHomeomorph M H) (x : ConnectedSumQuotient c d a)
    (hx : x ∈ leftTarget c d a f) : leftWitness c d a f x hx ∈ leftRegion c f :=
  (Classical.choose_spec (leftTargetExists c d a f x hx)).1

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.leftWitness_mem with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.leftWitness_mem"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.leftWitness_mem ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.leftWitness_mem

theorem inl_leftWitness (f : OpenPartialHomeomorph M H) (x : ConnectedSumQuotient c d a)
    (hx : x ∈ leftTarget c d a f) : inl c d a (leftWitness c d a f x hx) = x :=
  (Classical.choose_spec (leftTargetExists c d a f x hx)).2

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.inl_leftWitness with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.inl_leftWitness"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.inl_leftWitness ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.inl_leftWitness

variable [Nonempty H]

def leftInvFun (f : OpenPartialHomeomorph M H) :
    ConnectedSumQuotient c d a → H :=
  fun x => if h : x ∈ leftTarget c d a f then
    f ((leftWitness c d a f x h : c.Punctured) : M) else Classical.arbitrary H

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.leftInvFun with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.leftInvFun"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.leftInvFun ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.leftInvFun

theorem leftInvFun_of_mem (f : OpenPartialHomeomorph M H) (x : ConnectedSumQuotient c d a)
    (hx : x ∈ leftTarget c d a f) :
    leftInvFun c d a f x = f ((leftWitness c d a f x hx : c.Punctured) : M) := by
  rw [leftInvFun, dif_pos hx]

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.leftInvFun_of_mem with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.leftInvFun_of_mem"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.leftInvFun_of_mem ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.leftInvFun_of_mem

def leftPartialEquiv (hn : 0 < n) (f : OpenPartialHomeomorph M H) :
    PartialEquiv H (ConnectedSumQuotient c d a) where
  toFun := leftToFun c d a hn f
  invFun := leftInvFun c d a f
  source := leftChartSource c f
  target := leftTarget c d a f
  map_source' := by
    intro y hy
    exact ⟨leftCoord c hn f y, leftCoord_mem_leftRegion c hn f y hy, rfl⟩
  map_target' := by
    intro x hx
    rw [leftInvFun_of_mem c d a f x hx]
    exact ⟨(leftWitness c d a f x hx : c.Punctured),
      leftWitness_mem c d a f x hx, rfl⟩
  left_inv' := by
    intro y hy
    have hx : leftToFun c d a hn f y ∈ leftTarget c d a f :=
      ⟨leftCoord c hn f y, leftCoord_mem_leftRegion c hn f y hy, rfl⟩
    rw [leftInvFun_of_mem c d a f _ hx]
    have hchoose : (leftWitness c d a f (leftToFun c d a hn f y) hx : c.Punctured) =
        leftCoord c hn f y :=
      inl_injective c d a (inl_leftWitness c d a f _ hx)
    rw [hchoose, leftCoord_val_of_mem c hn f y hy]
    exact f.right_inv (leftChartSource_subset_target c f hy)
  right_inv' := by
    intro x hx
    rw [leftInvFun_of_mem c d a f x hx]
    set p := leftWitness c d a f x hx
    have hp : p ∈ leftRegion c f := leftWitness_mem c d a f x hx
    have hpx : inl c d a p = x := inl_leftWitness c d a f x hx
    have hsrc : f (p : M) ∈ leftChartSource c f :=
      ⟨(p : M), ⟨hp.1, hp.2⟩, rfl⟩
    have hcoord : leftCoord c hn f (f (p : M)) = p := by
      apply Subtype.ext
      rw [leftCoord_val_of_mem c hn f (f (p : M)) hsrc, f.left_inv hp.1]
    rw [leftToFun, hcoord]
    exact hpx

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.leftPartialEquiv with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.leftPartialEquiv"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.leftPartialEquiv ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.leftPartialEquiv

def leftChart (hn : 0 < n) (f : OpenPartialHomeomorph M H) :
    OpenPartialHomeomorph H (ConnectedSumQuotient c d a) :=
  OpenPartialHomeomorph.ofContinuousOpenRestrict (leftPartialEquiv c d a hn f)
    (leftToFun_continuousOn c d a hn f) (leftToFun_openMap c d a hn f)
    (isOpen_leftChartSource c f)

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.leftChart with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.leftChart"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.leftChart ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.leftChart

@[simp]
theorem leftChart_source (hn : 0 < n) (f : OpenPartialHomeomorph M H) :
    (leftChart c d a hn f).source = leftChartSource c f := rfl

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.leftChart_source with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.leftChart_source"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.leftChart_source ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.leftChart_source

@[simp]
theorem leftChart_target (hn : 0 < n) (f : OpenPartialHomeomorph M H) :
    (leftChart c d a hn f).target = leftTarget c d a f := rfl

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.leftChart_target with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.leftChart_target"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.leftChart_target ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.leftChart_target

@[simp]
theorem leftChart_apply (hn : 0 < n) (f : OpenPartialHomeomorph M H) (y : H) :
    leftChart c d a hn f y = inl c d a (leftCoord c hn f y) := rfl

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.leftChart_apply with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.leftChart_apply"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.leftChart_apply ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.leftChart_apply

theorem leftChart_symm_apply_inl (hn : 0 < n) (f : OpenPartialHomeomorph M H)
    {p : c.Punctured} (hp : p ∈ leftRegion c f) :
    (leftChart c d a hn f).symm (inl c d a p) = f (p : M) := by
  have hx : inl c d a p ∈ leftTarget c d a f := ⟨p, hp, rfl⟩
  change leftInvFun c d a f (inl c d a p) = f (p : M)
  rw [leftInvFun_of_mem c d a f (inl c d a p) hx]
  have hchoose : (leftWitness c d a f (inl c d a p) hx : c.Punctured) = p :=
    inl_injective c d a (inl_leftWitness c d a f (inl c d a p) hx)
  rw [hchoose]

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.leftChart_symm_apply_inl with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.leftChart_symm_apply_inl"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.leftChart_symm_apply_inl ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.leftChart_symm_apply_inl

theorem mem_leftChart_target_of_mem_source (hn : 0 < n) (f : OpenPartialHomeomorph M H)
    {u : c.interior} (hu : (u : M) ∈ f.source) :
    inl c d a (c.interiorToPunctured u) ∈ (leftChart c d a hn f).target := by
  have hmem : f (u : M) ∈ leftChartSource c f := ⟨(u : M), ⟨hu, u.2⟩, rfl⟩
  rw [leftChart_target]
  refine ⟨leftCoord c hn f (f (u : M)), leftCoord_mem_leftRegion c hn f _ hmem, ?_⟩
  refine congrArg (inl c d a) (Subtype.ext ?_)
  rw [leftCoord_val_of_mem c hn f (f (u : M)) hmem, f.left_inv hu]
  exact (BallChart.interiorToPunctured_val c u).symm

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.mem_leftChart_target_of_mem_source with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.mem_leftChart_target_of_mem_source"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.mem_leftChart_target_of_mem_source ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.mem_leftChart_target_of_mem_source

theorem exists_leftChart_mem_target_of_interior (hn : 0 < n) (u : c.interior) :
    ∃ f : OpenPartialHomeomorph M H, f ∈ atlas H M ∧
      inl c d a (c.interiorToPunctured u) ∈ (leftChart c d a hn f).target :=
  ⟨chartAt H (u : M), chart_mem_atlas H _, mem_leftChart_target_of_mem_source c d a hn _
    (mem_chart_source H (u : M))⟩

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.exists_leftChart_mem_target_of_interior with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.exists_leftChart_mem_target_of_interior"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.exists_leftChart_mem_target_of_interior ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.exists_leftChart_mem_target_of_interior

end Left

section Right

variable [T2Space N]

def rightRegion (g : OpenPartialHomeomorph N K) : Set d.Punctured :=
  Subtype.val ⁻¹' (g.source ∩ (d.interior : Set N))

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.rightRegion with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.rightRegion"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.rightRegion ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.rightRegion

@[simp]
theorem mem_rightRegion (g : OpenPartialHomeomorph N K) (q : d.Punctured) :
    q ∈ rightRegion d g ↔ (q : N) ∈ g.source ∧ (q : N) ∈ (d.interior : Set N) :=
  Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.mem_rightRegion with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.mem_rightRegion"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.mem_rightRegion ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.mem_rightRegion

theorem isOpen_rightRegion (g : OpenPartialHomeomorph N K) : IsOpen (rightRegion d g) :=
  (g.open_source.inter d.interior.isOpen).preimage continuous_subtype_val

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.isOpen_rightRegion with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.isOpen_rightRegion"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.isOpen_rightRegion ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.isOpen_rightRegion

theorem rightRegion_disjoint_seam (g : OpenPartialHomeomorph N K) :
    ∀ z, d.boundaryMap z ∉ rightRegion d g := by
  intro z hq
  have hmem : (d.boundaryMap z : N) ∈ d.chart '' Metric.closedBall 0 1 :=
    ⟨(z : EuclideanSpace ℝ (Fin n)),
      by simp [Metric.mem_closedBall],
      rfl⟩
  exact (BallChart.mem_interior (c := d)).mp hq.2 hmem

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.rightRegion_disjoint_seam with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.rightRegion_disjoint_seam"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.rightRegion_disjoint_seam ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.rightRegion_disjoint_seam

def rightTarget (g : OpenPartialHomeomorph N K) : Set (ConnectedSumQuotient c d a) :=
  inr c d a '' rightRegion d g

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.rightTarget with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.rightTarget"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.rightTarget ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.rightTarget

theorem mem_rightTarget (g : OpenPartialHomeomorph N K) (x : ConnectedSumQuotient c d a) :
    x ∈ rightTarget c d a g ↔ ∃ q : d.Punctured, q ∈ rightRegion d g ∧ inr c d a q = x :=
  Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.mem_rightTarget with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.mem_rightTarget"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.mem_rightTarget ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.mem_rightTarget

theorem isOpen_rightTarget (g : OpenPartialHomeomorph N K) : IsOpen (rightTarget c d a g) :=
  isOpen_image_inr c d a (isOpen_rightRegion d g) (rightRegion_disjoint_seam d g)

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.isOpen_rightTarget with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.isOpen_rightTarget"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.isOpen_rightTarget ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.isOpen_rightTarget

def rightChartSource (g : OpenPartialHomeomorph N K) : Set K :=
  g '' (g.source ∩ (d.interior : Set N))

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.rightChartSource with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.rightChartSource"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.rightChartSource ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.rightChartSource

theorem mem_rightChartSource (g : OpenPartialHomeomorph N K) (z : K) :
    z ∈ rightChartSource d g ↔ z ∈ g.target ∧ g.symm z ∈ (d.interior : Set N) := by
  constructor
  · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
    refine ⟨g.map_source hx1, ?_⟩
    rwa [g.left_inv hx1]
  · rintro ⟨hz, hzs⟩
    exact ⟨g.symm z, ⟨g.map_target hz, hzs⟩, g.right_inv hz⟩

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.mem_rightChartSource with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.mem_rightChartSource"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.mem_rightChartSource ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.mem_rightChartSource

theorem isOpen_rightChartSource (g : OpenPartialHomeomorph N K) :
    IsOpen (rightChartSource d g) :=
  g.isOpen_image_of_subset_source (g.open_source.inter d.interior.isOpen) Set.inter_subset_left

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.isOpen_rightChartSource with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.isOpen_rightChartSource"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.isOpen_rightChartSource ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.isOpen_rightChartSource

theorem rightChartSource_subset_target (g : OpenPartialHomeomorph N K) :
    rightChartSource d g ⊆ g.target :=
  fun _ hz => ((mem_rightChartSource d g _).mp hz).1

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.rightChartSource_subset_target with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.rightChartSource_subset_target"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.rightChartSource_subset_target ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.rightChartSource_subset_target

theorem symm_mem_of_mem_rightChartSource (g : OpenPartialHomeomorph N K) (z : K)
    (hz : z ∈ rightChartSource d g) :
    g.symm z ∈ g.source ∩ (d.interior : Set N) := by
  obtain ⟨x, ⟨hx1, hx2⟩, hxz⟩ := hz
  rw [← hxz, g.left_inv hx1]
  exact ⟨hx1, hx2⟩

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.symm_mem_of_mem_rightChartSource with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.symm_mem_of_mem_rightChartSource"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.symm_mem_of_mem_rightChartSource ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.symm_mem_of_mem_rightChartSource

def rightCoord (hn : 0 < n) (g : OpenPartialHomeomorph N K) (z : K) : d.Punctured :=
  if h : z ∈ rightChartSource d g then
    ⟨g.symm z, fun hmem =>
      (BallChart.mem_interior (c := d)).mp (symm_mem_of_mem_rightChartSource d g z h).2
        (Set.image_mono Metric.ball_subset_closedBall hmem)⟩
  else rightDefault d hn

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.rightCoord with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.rightCoord"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.rightCoord ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.rightCoord

theorem rightCoord_val_of_mem (hn : 0 < n) (g : OpenPartialHomeomorph N K) (z : K)
    (hz : z ∈ rightChartSource d g) : (rightCoord d hn g z : N) = g.symm z := by
  rw [rightCoord, dif_pos hz]

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.rightCoord_val_of_mem with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.rightCoord_val_of_mem"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.rightCoord_val_of_mem ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.rightCoord_val_of_mem

theorem rightCoord_mem_rightRegion (hn : 0 < n) (g : OpenPartialHomeomorph N K) (z : K)
    (hz : z ∈ rightChartSource d g) : rightCoord d hn g z ∈ rightRegion d g := by
  rw [mem_rightRegion]
  obtain ⟨h1, h2⟩ := symm_mem_of_mem_rightChartSource d g z hz
  exact ⟨by rw [rightCoord_val_of_mem d hn g z hz]; exact h1,
    by rw [rightCoord_val_of_mem d hn g z hz]; exact h2⟩

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.rightCoord_mem_rightRegion with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.rightCoord_mem_rightRegion"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.rightCoord_mem_rightRegion ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.rightCoord_mem_rightRegion

def rightToFun (hn : 0 < n) (g : OpenPartialHomeomorph N K) :
    K → ConnectedSumQuotient c d a :=
  fun z => inr c d a (rightCoord d hn g z)

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.rightToFun with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.rightToFun"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.rightToFun ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.rightToFun

def rightSubtypeMap (g : OpenPartialHomeomorph N K) :
    ↥(rightChartSource d g) → d.Punctured :=
  fun z => ⟨g.symm (z : K), fun hmem =>
    (BallChart.mem_interior (c := d)).mp
      (symm_mem_of_mem_rightChartSource d g (z : K) z.2).2
      (Set.image_mono Metric.ball_subset_closedBall hmem)⟩

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.rightSubtypeMap with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.rightSubtypeMap"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.rightSubtypeMap ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.rightSubtypeMap

theorem rightSubtypeMap_val (g : OpenPartialHomeomorph N K) (z : ↥(rightChartSource d g)) :
    (rightSubtypeMap d g z : N) = g.symm (z : K) := rfl

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.rightSubtypeMap_val with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.rightSubtypeMap_val"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.rightSubtypeMap_val ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.rightSubtypeMap_val

theorem rightCoord_eq_rightSubtypeMap (hn : 0 < n) (g : OpenPartialHomeomorph N K)
    (z : ↥(rightChartSource d g)) :
    rightCoord d hn g (z : K) = rightSubtypeMap d g z :=
  Subtype.ext (rightCoord_val_of_mem d hn g (z : K) z.2)

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.rightCoord_eq_rightSubtypeMap with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.rightCoord_eq_rightSubtypeMap"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.rightCoord_eq_rightSubtypeMap ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.rightCoord_eq_rightSubtypeMap

theorem rightToFun_comp_subtype_val (hn : 0 < n) (g : OpenPartialHomeomorph N K) :
    rightToFun c d a hn g ∘ (Subtype.val : ↥(rightChartSource d g) → K) =
      inr c d a ∘ rightSubtypeMap d g := by
  funext z
  exact congrArg (inr c d a) (rightCoord_eq_rightSubtypeMap d hn g z)

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.rightToFun_comp_subtype_val with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.rightToFun_comp_subtype_val"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.rightToFun_comp_subtype_val ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.rightToFun_comp_subtype_val

theorem rightSubtypeMap_continuous (g : OpenPartialHomeomorph N K) :
    Continuous (rightSubtypeMap d g) := by
  have hbase : Continuous fun z : ↥(rightChartSource d g) => g.symm (z : K) :=
    g.continuousOn_symm.comp_continuous continuous_subtype_val
      (fun z => rightChartSource_subset_target d g z.2)
  exact hbase.subtype_mk _

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.rightSubtypeMap_continuous with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.rightSubtypeMap_continuous"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.rightSubtypeMap_continuous ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.rightSubtypeMap_continuous

theorem rightToFun_continuousOn (hn : 0 < n) (g : OpenPartialHomeomorph N K) :
    ContinuousOn (rightToFun c d a hn g) (rightChartSource d g) := by
  rw [continuousOn_iff_continuous_domRestrict]
  refine ((continuous_inr c d a).comp (rightSubtypeMap_continuous d g)).congr fun z => ?_
  exact congrArg (inr c d a) (rightCoord_eq_rightSubtypeMap d hn g z).symm

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.rightToFun_continuousOn with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.rightToFun_continuousOn"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.rightToFun_continuousOn ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.rightToFun_continuousOn

theorem rightSubtypeMap_image_subset (g : OpenPartialHomeomorph N K)
    (V : Set ↥(rightChartSource d g)) : rightSubtypeMap d g '' V ⊆ rightRegion d g := by
  rintro q ⟨z, -, rfl⟩
  rw [mem_rightRegion]
  exact symm_mem_of_mem_rightChartSource d g (z : K) z.2

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.rightSubtypeMap_image_subset with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.rightSubtypeMap_image_subset"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.rightSubtypeMap_image_subset ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.rightSubtypeMap_image_subset

theorem isOpen_rightSubtypeMap_image (g : OpenPartialHomeomorph N K)
    {V : Set ↥(rightChartSource d g)} (hV : IsOpen V) :
    IsOpen (rightSubtypeMap d g '' V) := by
  have hVopen : IsOpen ((Subtype.val : ↥(rightChartSource d g) → K) '' V) :=
    (isOpen_rightChartSource d g).isOpenEmbedding_subtypeVal.isOpenMap V hV
  have hW : IsOpen (g.symm '' ((Subtype.val : ↥(rightChartSource d g) → K) '' V)) :=
    g.isOpen_image_symm_of_subset_target hVopen (by
      rintro z ⟨y, -, rfl⟩
      exact rightChartSource_subset_target d g y.2)
  have heq : rightSubtypeMap d g '' V =
      Subtype.val ⁻¹' (g.symm '' ((Subtype.val : ↥(rightChartSource d g) → K) '' V)) := by
    ext q
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨(z : K), ⟨z, hz, rfl⟩, rfl⟩
    · rintro ⟨w, ⟨z, hz, rfl⟩, hwq⟩
      exact ⟨z, hz, Subtype.ext hwq⟩
  rw [heq]
  exact hW.preimage continuous_subtype_val

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.isOpen_rightSubtypeMap_image with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.isOpen_rightSubtypeMap_image"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.isOpen_rightSubtypeMap_image ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.isOpen_rightSubtypeMap_image

theorem rightToFun_openMap (hn : 0 < n) (g : OpenPartialHomeomorph N K) :
    IsOpenMap ((rightChartSource d g).domRestrict (rightToFun c d a hn g)) := by
  intro V hV
  have himg : (rightChartSource d g).domRestrict (rightToFun c d a hn g) '' V =
      rightToFun c d a hn g '' ((Subtype.val : ↥(rightChartSource d g) → K) '' V) := by
    ext x
    constructor
    · rintro ⟨z, hz, hxz⟩
      exact ⟨(z : K), ⟨z, hz, rfl⟩, hxz⟩
    · rintro ⟨w, ⟨z, hz, hzw⟩, hwx⟩
      refine ⟨z, hz, ?_⟩
      change rightToFun c d a hn g (z : K) = x
      rw [hzw]
      exact hwx
  rw [himg]
  rw [← Set.image_comp, rightToFun_comp_subtype_val c d a hn g, Set.image_comp]
  refine isOpen_image_inr c d a (isOpen_rightSubtypeMap_image d g hV) ?_
  exact fun z hz => rightRegion_disjoint_seam d g z (rightSubtypeMap_image_subset d g V hz)

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.rightToFun_openMap with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.rightToFun_openMap"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.rightToFun_openMap ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.rightToFun_openMap

theorem rightTargetExists (g : OpenPartialHomeomorph N K) (x : ConnectedSumQuotient c d a)
    (hx : x ∈ rightTarget c d a g) :
    ∃ q : d.Punctured, q ∈ rightRegion d g ∧ inr c d a q = x :=
  (mem_rightTarget c d a g x).mp hx

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.rightTargetExists with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.rightTargetExists"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.rightTargetExists ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.rightTargetExists

def rightWitness (g : OpenPartialHomeomorph N K) (x : ConnectedSumQuotient c d a)
    (hx : x ∈ rightTarget c d a g) : d.Punctured :=
  Classical.choose (rightTargetExists c d a g x hx)

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.rightWitness with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.rightWitness"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.rightWitness ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.rightWitness

theorem rightWitness_mem (g : OpenPartialHomeomorph N K) (x : ConnectedSumQuotient c d a)
    (hx : x ∈ rightTarget c d a g) : rightWitness c d a g x hx ∈ rightRegion d g :=
  (Classical.choose_spec (rightTargetExists c d a g x hx)).1

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.rightWitness_mem with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.rightWitness_mem"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.rightWitness_mem ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.rightWitness_mem

theorem inr_rightWitness (g : OpenPartialHomeomorph N K) (x : ConnectedSumQuotient c d a)
    (hx : x ∈ rightTarget c d a g) : inr c d a (rightWitness c d a g x hx) = x :=
  (Classical.choose_spec (rightTargetExists c d a g x hx)).2

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.inr_rightWitness with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.inr_rightWitness"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.inr_rightWitness ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.inr_rightWitness

variable [Nonempty K]

def rightInvFun (g : OpenPartialHomeomorph N K) :
    ConnectedSumQuotient c d a → K :=
  fun x => if h : x ∈ rightTarget c d a g then
    g ((rightWitness c d a g x h : d.Punctured) : N) else Classical.arbitrary K

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.rightInvFun with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.rightInvFun"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.rightInvFun ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.rightInvFun

theorem rightInvFun_of_mem (g : OpenPartialHomeomorph N K) (x : ConnectedSumQuotient c d a)
    (hx : x ∈ rightTarget c d a g) :
    rightInvFun c d a g x = g ((rightWitness c d a g x hx : d.Punctured) : N) := by
  rw [rightInvFun, dif_pos hx]

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.rightInvFun_of_mem with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.rightInvFun_of_mem"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.rightInvFun_of_mem ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.rightInvFun_of_mem

def rightPartialEquiv (hn : 0 < n) (g : OpenPartialHomeomorph N K) :
    PartialEquiv K (ConnectedSumQuotient c d a) where
  toFun := rightToFun c d a hn g
  invFun := rightInvFun c d a g
  source := rightChartSource d g
  target := rightTarget c d a g
  map_source' := by
    intro z hz
    exact ⟨rightCoord d hn g z, rightCoord_mem_rightRegion d hn g z hz, rfl⟩
  map_target' := by
    intro x hx
    rw [rightInvFun_of_mem c d a g x hx]
    exact ⟨(rightWitness c d a g x hx : d.Punctured),
      rightWitness_mem c d a g x hx, rfl⟩
  left_inv' := by
    intro z hz
    have hx : rightToFun c d a hn g z ∈ rightTarget c d a g :=
      ⟨rightCoord d hn g z, rightCoord_mem_rightRegion d hn g z hz, rfl⟩
    rw [rightInvFun_of_mem c d a g _ hx]
    have hchoose : (rightWitness c d a g (rightToFun c d a hn g z) hx : d.Punctured) =
        rightCoord d hn g z :=
      inr_injective c d a (inr_rightWitness c d a g _ hx)
    rw [hchoose, rightCoord_val_of_mem d hn g z hz]
    exact g.right_inv (rightChartSource_subset_target d g hz)
  right_inv' := by
    intro x hx
    rw [rightInvFun_of_mem c d a g x hx]
    set q := rightWitness c d a g x hx
    have hq : q ∈ rightRegion d g := rightWitness_mem c d a g x hx
    have hqx : inr c d a q = x := inr_rightWitness c d a g x hx
    have hsrc : g (q : N) ∈ rightChartSource d g := ⟨(q : N), ⟨hq.1, hq.2⟩, rfl⟩
    have hcoord : rightCoord d hn g (g (q : N)) = q := by
      apply Subtype.ext
      rw [rightCoord_val_of_mem d hn g (g (q : N)) hsrc, g.left_inv hq.1]
    rw [rightToFun, hcoord]
    exact hqx

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.rightPartialEquiv with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.rightPartialEquiv"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.rightPartialEquiv ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.rightPartialEquiv

def rightChart (hn : 0 < n) (g : OpenPartialHomeomorph N K) :
    OpenPartialHomeomorph K (ConnectedSumQuotient c d a) :=
  OpenPartialHomeomorph.ofContinuousOpenRestrict (rightPartialEquiv c d a hn g)
    (rightToFun_continuousOn c d a hn g) (rightToFun_openMap c d a hn g)
    (isOpen_rightChartSource d g)

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.rightChart with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.rightChart"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.rightChart ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.rightChart

@[simp]
theorem rightChart_source (hn : 0 < n) (g : OpenPartialHomeomorph N K) :
    (rightChart c d a hn g).source = rightChartSource d g := rfl

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.rightChart_source with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.rightChart_source"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.rightChart_source ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.rightChart_source

@[simp]
theorem rightChart_target (hn : 0 < n) (g : OpenPartialHomeomorph N K) :
    (rightChart c d a hn g).target = rightTarget c d a g := rfl

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.rightChart_target with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.rightChart_target"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.rightChart_target ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.rightChart_target

@[simp]
theorem rightChart_apply (hn : 0 < n) (g : OpenPartialHomeomorph N K) (z : K) :
    rightChart c d a hn g z = inr c d a (rightCoord d hn g z) := rfl

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.rightChart_apply with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.rightChart_apply"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.rightChart_apply ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.rightChart_apply

theorem rightChart_symm_apply_inr (hn : 0 < n) (g : OpenPartialHomeomorph N K)
    {q : d.Punctured} (hq : q ∈ rightRegion d g) :
    (rightChart c d a hn g).symm (inr c d a q) = g (q : N) := by
  have hx : inr c d a q ∈ rightTarget c d a g := ⟨q, hq, rfl⟩
  change rightInvFun c d a g (inr c d a q) = g (q : N)
  rw [rightInvFun_of_mem c d a g (inr c d a q) hx]
  have hchoose : (rightWitness c d a g (inr c d a q) hx : d.Punctured) = q :=
    inr_injective c d a (inr_rightWitness c d a g (inr c d a q) hx)
  rw [hchoose]

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.rightChart_symm_apply_inr with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.rightChart_symm_apply_inr"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.rightChart_symm_apply_inr ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.rightChart_symm_apply_inr

theorem mem_rightChart_target_of_mem_source (hn : 0 < n) (g : OpenPartialHomeomorph N K)
    {v : d.interior} (hv : (v : N) ∈ g.source) :
    inr c d a (d.interiorToPunctured v) ∈ (rightChart c d a hn g).target := by
  have hmem : g (v : N) ∈ rightChartSource d g := ⟨(v : N), ⟨hv, v.2⟩, rfl⟩
  rw [rightChart_target]
  refine ⟨rightCoord d hn g (g (v : N)), rightCoord_mem_rightRegion d hn g _ hmem, ?_⟩
  refine congrArg (inr c d a) (Subtype.ext ?_)
  rw [rightCoord_val_of_mem d hn g (g (v : N)) hmem, g.left_inv hv]
  exact (BallChart.interiorToPunctured_val d v).symm

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.mem_rightChart_target_of_mem_source with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.mem_rightChart_target_of_mem_source"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.mem_rightChart_target_of_mem_source ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.mem_rightChart_target_of_mem_source

theorem exists_rightChart_mem_target_of_interior (hn : 0 < n) (v : d.interior) :
    ∃ g : OpenPartialHomeomorph N K, g ∈ atlas K N ∧
      inr c d a (d.interiorToPunctured v) ∈ (rightChart c d a hn g).target :=
  ⟨chartAt K (v : N), chart_mem_atlas K _, mem_rightChart_target_of_mem_source c d a hn _
    (mem_chart_source K (v : N))⟩

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.exists_rightChart_mem_target_of_interior with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.exists_rightChart_mem_target_of_interior"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.exists_rightChart_mem_target_of_interior ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.exists_rightChart_mem_target_of_interior

end Right

section CoverageAll

variable [T2Space M] [T2Space N] [Nonempty H] [Nonempty K]

theorem exists_chart_mem_target_of_mem_interior (hn : 0 < n) (x : ConnectedSumQuotient c d a)
    (hx : (∃ u : c.interior, inl c d a (c.interiorToPunctured u) = x) ∨
      (∃ v : d.interior, inr c d a (d.interiorToPunctured v) = x)) :
    (∃ f : OpenPartialHomeomorph M H, f ∈ atlas H M ∧ x ∈ (leftChart c d a hn f).target) ∨
      ∃ g : OpenPartialHomeomorph N K, g ∈ atlas K N ∧ x ∈ (rightChart c d a hn g).target := by
  rcases hx with ⟨u, rfl⟩ | ⟨v, rfl⟩
  · exact Or.inl (exists_leftChart_mem_target_of_interior c d a hn u)
  · exact Or.inr (exists_rightChart_mem_target_of_interior c d a hn v)

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.exists_chart_mem_target_of_mem_interior with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.exists_chart_mem_target_of_mem_interior"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.exists_chart_mem_target_of_mem_interior ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.exists_chart_mem_target_of_mem_interior

end CoverageAll

section CoverageLeft

variable [T2Space M] [Nonempty H]

theorem leftChart_target_subset_interiorLeft (hn : 0 < n) (f : OpenPartialHomeomorph M H) :
    (leftChart c d a hn f).target ⊆
      inl c d a '' (c.interiorToPunctured '' Set.univ) := by
  intro x hx
  rw [leftChart_target] at hx
  obtain ⟨p, hp, rfl⟩ := (mem_leftTarget c d a f x).mp hx
  refine ⟨c.interiorToPunctured ⟨(p : M), hp.2⟩,
    ⟨⟨(p : M), hp.2⟩, Set.mem_univ _, rfl⟩, ?_⟩
  exact congrArg (inl c d a) (Subtype.ext rfl)

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.leftChart_target_subset_interiorLeft with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.leftChart_target_subset_interiorLeft"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.leftChart_target_subset_interiorLeft ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.leftChart_target_subset_interiorLeft

end CoverageLeft

section ChartOnManifold

variable [T2Space M] [Nonempty H]

def leftChartOnManifold (hn : 0 < n) (f : OpenPartialHomeomorph M H) :
    OpenPartialHomeomorph M (ConnectedSumQuotient c d a) :=
  f.trans (leftChart c d a hn f)

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.leftChartOnManifold with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.leftChartOnManifold"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.leftChartOnManifold ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.leftChartOnManifold

theorem leftChartOnManifold_source (hn : 0 < n) (f : OpenPartialHomeomorph M H) :
    (leftChartOnManifold c d a hn f).source = f.source ∩ (c.interior : Set M) := by
  rw [leftChartOnManifold, OpenPartialHomeomorph.trans_source]
  ext x
  constructor
  · rintro ⟨hx1, hx2⟩
    refine ⟨hx1, ?_⟩
    obtain ⟨-, hxs⟩ := (mem_leftChartSource c f (f x)).mp hx2
    simpa [f.left_inv hx1] using hxs
  · rintro ⟨hx1, hx2⟩
    exact ⟨hx1, (mem_leftChartSource c f (f x)).mpr
      ⟨f.map_source hx1, by simpa [f.left_inv hx1] using hx2⟩⟩

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.leftChartOnManifold_source with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.leftChartOnManifold_source"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.leftChartOnManifold_source ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.leftChartOnManifold_source

theorem leftChartOnManifold_apply (hn : 0 < n) (f : OpenPartialHomeomorph M H) {x : M}
    (hx : x ∈ f.source ∩ (c.interior : Set M)) :
    leftChartOnManifold c d a hn f x =
      inl c d a (c.interiorToPunctured ⟨x, hx.2⟩) := by
  have hsrc : f x ∈ leftChartSource c f := ⟨x, hx, rfl⟩
  rw [leftChartOnManifold, OpenPartialHomeomorph.trans_apply, leftChart_apply]
  refine congrArg (inl c d a) (Subtype.ext ?_)
  rw [leftCoord_val_of_mem c hn f (f x) hsrc, f.left_inv hx.1]
  rfl

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.leftChartOnManifold_apply with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.leftChartOnManifold_apply"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.leftChartOnManifold_apply ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.leftChartOnManifold_apply

end ChartOnManifold

section CoverageRight

variable [T2Space N] [Nonempty K]

theorem rightChart_target_subset_interiorRight (hn : 0 < n) (g : OpenPartialHomeomorph N K) :
    (rightChart c d a hn g).target ⊆
      inr c d a '' (d.interiorToPunctured '' Set.univ) := by
  intro x hx
  rw [rightChart_target] at hx
  obtain ⟨q, hq, rfl⟩ := (mem_rightTarget c d a g x).mp hx
  refine ⟨d.interiorToPunctured ⟨(q : N), hq.2⟩,
    ⟨⟨(q : N), hq.2⟩, Set.mem_univ _, rfl⟩, ?_⟩
  exact congrArg (inr c d a) (Subtype.ext rfl)

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.rightChart_target_subset_interiorRight with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.rightChart_target_subset_interiorRight"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.rightChart_target_subset_interiorRight ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.rightChart_target_subset_interiorRight

end CoverageRight

section DisjointTargets

variable [T2Space M] [T2Space N]

theorem disjoint_leftTarget_rightTarget (f : OpenPartialHomeomorph M H)
    (g : OpenPartialHomeomorph N K) :
    Disjoint (leftTarget c d a f) (rightTarget c d a g) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  obtain ⟨p, hp, rfl⟩ := (mem_leftTarget c d a f x).mp hx
  obtain ⟨q, hq, hqeq⟩ := (mem_rightTarget c d a g (inl c d a p)).mp hx'
  obtain ⟨z, hz, -⟩ := (inl_eq_inr_iff c d a p q).mp hqeq.symm
  exact leftRegion_disjoint_seam c f z (hz ▸ hp)

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.disjoint_leftTarget_rightTarget with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.disjoint_leftTarget_rightTarget"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.disjoint_leftTarget_rightTarget ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.disjoint_leftTarget_rightTarget

end DisjointTargets

section DisjointTargetsCharts

variable [T2Space M] [T2Space N] [Nonempty H] [Nonempty K]

theorem leftChart_trans_rightChart_source_eq_empty (hn : 0 < n)
    (f : OpenPartialHomeomorph M H) (g : OpenPartialHomeomorph N K) :
    ((leftChart c d a hn f).trans (rightChart c d a hn g).symm).source = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem, OpenPartialHomeomorph.trans_source]
  rintro y ⟨hy1, hy2⟩
  exact (Set.disjoint_left.mp (disjoint_leftTarget_rightTarget c d a f g))
    ((leftChart c d a hn f).map_source hy1) (by simpa using hy2)

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.leftChart_trans_rightChart_source_eq_empty with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.leftChart_trans_rightChart_source_eq_empty"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.leftChart_trans_rightChart_source_eq_empty ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.leftChart_trans_rightChart_source_eq_empty

theorem rightChart_trans_leftChart_source_eq_empty (hn : 0 < n)
    (g : OpenPartialHomeomorph N K) (f : OpenPartialHomeomorph M H) :
    ((rightChart c d a hn g).trans (leftChart c d a hn f).symm).source = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem, OpenPartialHomeomorph.trans_source]
  rintro y ⟨hy1, hy2⟩
  exact (Set.disjoint_left.mp (disjoint_leftTarget_rightTarget c d a f g).symm)
    ((rightChart c d a hn g).map_source hy1) (by simpa using hy2)

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.rightChart_trans_leftChart_source_eq_empty with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.rightChart_trans_leftChart_source_eq_empty"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.rightChart_trans_leftChart_source_eq_empty ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.rightChart_trans_leftChart_source_eq_empty

end DisjointTargetsCharts

section Transition

variable [T2Space M] [Nonempty H]

theorem leftChart_trans_apply_eq (hn : 0 < n) (f g : OpenPartialHomeomorph M H) {y : H}
    (hy : y ∈ ((leftChart c d a hn f).trans (leftChart c d a hn g).symm).source) :
    ((leftChart c d a hn f).trans (leftChart c d a hn g).symm) y = g (f.symm y) := by
  rw [OpenPartialHomeomorph.trans_source] at hy
  have hy1 : y ∈ (leftChart c d a hn f).source := hy.1
  have hy2 : (leftChart c d a hn f) y ∈ (leftChart c d a hn g).target := by
    simpa using hy.2
  have hcoord : leftCoord c hn f y ∈ leftRegion c g := by
    obtain ⟨q, hq, hqeq⟩ := (mem_leftTarget c d a g ((leftChart c d a hn f) y)).mp hy2
    have hq' : q = leftCoord c hn f y := by
      apply inl_injective c d a
      rw [hqeq, leftChart_apply c d a hn f]
    rwa [hq'] at hq
  rw [OpenPartialHomeomorph.trans_apply, leftChart_apply c d a hn f,
    leftChart_symm_apply_inl c d a hn g hcoord]
  exact congrArg g (leftCoord_val_of_mem c hn f y hy1)

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.leftChart_trans_apply_eq with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.leftChart_trans_apply_eq"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.leftChart_trans_apply_eq ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.leftChart_trans_apply_eq

theorem leftChart_trans_source_subset (hn : 0 < n) (f g : OpenPartialHomeomorph M H) :
    ((leftChart c d a hn f).trans (leftChart c d a hn g).symm).source ⊆
      (f.symm.trans g).source := by
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.trans_source]
  rintro y ⟨hy1, hy2⟩
  have hy2' : (leftChart c d a hn f) y ∈ (leftChart c d a hn g).target := by
    simpa using hy2
  refine ⟨leftChartSource_subset_target c f hy1, ?_⟩
  obtain ⟨q, hq, hqeq⟩ := (mem_leftTarget c d a g ((leftChart c d a hn f) y)).mp hy2'
  have hq' : q = leftCoord c hn f y := by
    apply inl_injective c d a
    rw [hqeq, leftChart_apply c d a hn f]
  rw [hq'] at hq
  rw [mem_leftRegion] at hq
  rw [leftCoord_val_of_mem c hn f y hy1] at hq
  exact hq.1

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.leftChart_trans_source_subset with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.leftChart_trans_source_subset"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.leftChart_trans_source_subset ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.leftChart_trans_source_subset

end Transition

section TransitionRight

variable [T2Space N] [Nonempty K]

theorem rightChart_trans_apply_eq (hn : 0 < n) (g h : OpenPartialHomeomorph N K) {z : K}
    (hz : z ∈ ((rightChart c d a hn g).trans (rightChart c d a hn h).symm).source) :
    ((rightChart c d a hn g).trans (rightChart c d a hn h).symm) z = h (g.symm z) := by
  rw [OpenPartialHomeomorph.trans_source] at hz
  have hz1 : z ∈ (rightChart c d a hn g).source := hz.1
  have hz2 : (rightChart c d a hn g) z ∈ (rightChart c d a hn h).target := by
    simpa using hz.2
  have hcoord : rightCoord d hn g z ∈ rightRegion d h := by
    obtain ⟨q, hq, hqeq⟩ := (mem_rightTarget c d a h ((rightChart c d a hn g) z)).mp hz2
    have hq' : q = rightCoord d hn g z := by
      apply inr_injective c d a
      rw [hqeq, rightChart_apply c d a hn g]
    rwa [hq'] at hq
  rw [OpenPartialHomeomorph.trans_apply, rightChart_apply c d a hn g,
    rightChart_symm_apply_inr c d a hn h hcoord]
  exact congrArg h (rightCoord_val_of_mem d hn g z hz1)

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.rightChart_trans_apply_eq with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.rightChart_trans_apply_eq"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.rightChart_trans_apply_eq ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.rightChart_trans_apply_eq

theorem rightChart_trans_source_subset (hn : 0 < n) (g h : OpenPartialHomeomorph N K) :
    ((rightChart c d a hn g).trans (rightChart c d a hn h).symm).source ⊆
      (g.symm.trans h).source := by
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.trans_source]
  rintro z ⟨hz1, hz2⟩
  have hz2' : (rightChart c d a hn g) z ∈ (rightChart c d a hn h).target := by
    simpa using hz2
  refine ⟨rightChartSource_subset_target d g hz1, ?_⟩
  obtain ⟨q, hq, hqeq⟩ := (mem_rightTarget c d a h ((rightChart c d a hn g) z)).mp hz2'
  have hq' : q = rightCoord d hn g z := by
    apply inr_injective c d a
    rw [hqeq, rightChart_apply c d a hn g]
  rw [hq'] at hq
  rw [mem_rightRegion] at hq
  rw [rightCoord_val_of_mem d hn g z hz1] at hq
  exact hq.1

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.rightChart_trans_source_subset with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.rightChart_trans_source_subset"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.rightChart_trans_source_subset ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.rightChart_trans_source_subset

end TransitionRight

section TransitionSmooth

variable [T2Space M] [Nonempty H] [IsManifold I ∞ M]

theorem contMDiffOn_leftChart_trans_leftChart (hn : 0 < n)
    (f g : OpenPartialHomeomorph M H) (hf : f ∈ atlas H M) (hg : g ∈ atlas H M) :
    ContMDiffOn I I ∞ ((leftChart c d a hn f).trans (leftChart c d a hn g).symm)
      ((leftChart c d a hn f).trans (leftChart c d a hn g).symm).source := by
  have hmem : f.symm.trans g ∈ contDiffGroupoid ∞ I :=
    StructureGroupoid.compatible (contDiffGroupoid ∞ I) hf hg
  have hsmooth : ContMDiffOn I I ∞ (f.symm.trans g) (f.symm.trans g).source :=
    contMDiffOn_of_mem_contDiffGroupoid hmem
  refine (hsmooth.mono (leftChart_trans_source_subset c d a hn f g)).congr ?_
  intro y hy
  rw [OpenPartialHomeomorph.trans_apply, OpenPartialHomeomorph.trans_apply]
  exact leftChart_trans_apply_eq c d a hn f g hy

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.contMDiffOn_leftChart_trans_leftChart with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.contMDiffOn_leftChart_trans_leftChart"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.contMDiffOn_leftChart_trans_leftChart ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.contMDiffOn_leftChart_trans_leftChart

end TransitionSmooth

section TransitionSmoothRight

variable [T2Space N] [Nonempty K] [IsManifold J ∞ N]

theorem contMDiffOn_rightChart_trans_rightChart (hn : 0 < n)
    (g h : OpenPartialHomeomorph N K) (hg : g ∈ atlas K N) (hh : h ∈ atlas K N) :
    ContMDiffOn J J ∞ ((rightChart c d a hn g).trans (rightChart c d a hn h).symm)
      ((rightChart c d a hn g).trans (rightChart c d a hn h).symm).source := by
  have hmem : g.symm.trans h ∈ contDiffGroupoid ∞ J :=
    StructureGroupoid.compatible (contDiffGroupoid ∞ J) hg hh
  have hsmooth : ContMDiffOn J J ∞ (g.symm.trans h) (g.symm.trans h).source :=
    contMDiffOn_of_mem_contDiffGroupoid hmem
  refine (hsmooth.mono (rightChart_trans_source_subset c d a hn g h)).congr ?_
  intro z hz
  rw [OpenPartialHomeomorph.trans_apply, OpenPartialHomeomorph.trans_apply]
  exact rightChart_trans_apply_eq c d a hn g h hz

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.contMDiffOn_rightChart_trans_rightChart with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.contMDiffOn_rightChart_trans_rightChart"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.contMDiffOn_rightChart_trans_rightChart ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.contMDiffOn_rightChart_trans_rightChart

end TransitionSmoothRight

end ConnectedSumQuotient

end DifferentialGeometry.Topology
