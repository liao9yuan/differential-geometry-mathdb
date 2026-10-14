import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Quotient
import Mathlib.Geometry.Manifold.Instances.Sphere

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.Manifold _root_.ContDiff

noncomputable section

namespace DifferentialGeometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

namespace BallChart

variable {n : ℕ} (c : BallChart n I M)

theorem closedBall_one_subset_source : Metric.closedBall 0 1 ⊆ c.chart.source := by
  intro x hx
  apply c.closedBall_subset_source
  change _root_.Dist.dist x 0 ≤ 2
  exact le_trans (Metric.mem_closedBall.mp hx) (by norm_num)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.closedBall_one_subset_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.closedBall_one_subset_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.closedBall_one_subset_source ``Submission.DifferentialGeometry.Topology.BallChart.closedBall_one_subset_source

theorem norm_radial (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    {r : ℝ} (hr : 0 ≤ r) : ‖r • (z : EuclideanSpace ℝ (Fin n))‖ = r := by
  have hz : ‖(z : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using z.2
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, hz, mul_one]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.norm_radial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.norm_radial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.norm_radial ``Submission.DifferentialGeometry.Topology.BallChart.norm_radial

def radialMap (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    (r : ℝ) (hr : r ∈ Set.Icc 1 2) : c.Punctured :=
  ⟨c.chart (r • (z : EuclideanSpace ℝ (Fin n))), by
    rintro ⟨x, hx, h⟩
    have hr0 : 0 ≤ r := le_trans (by norm_num) hr.1
    have hs : r • (z : EuclideanSpace ℝ (Fin n)) ∈ c.chart.source := by
      apply c.closedBall_subset_source
      change _root_.Dist.dist (r • (z : EuclideanSpace ℝ (Fin n))) 0 ≤ 2
      rw [dist_zero_right, norm_radial z hr0]
      exact hr.2
    have heq : x = r • (z : EuclideanSpace ℝ (Fin n)) :=
      c.chart.toPartialEquiv.injOn (c.ball_subset_source hx) hs h
    have hxnorm : ‖x‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hx
    rw [heq, norm_radial z hr0] at hxnorm
    exact (not_lt_of_ge hr.1) hxnorm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.radialMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.radialMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.radialMap ``Submission.DifferentialGeometry.Topology.BallChart.radialMap

@[simp]
theorem radialMap_val (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    (r : ℝ) (hr : r ∈ Set.Icc 1 2) :
    (c.radialMap z r hr : M) = c.chart (r • (z : EuclideanSpace ℝ (Fin n))) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.radialMap_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.radialMap_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.radialMap_val ``Submission.DifferentialGeometry.Topology.BallChart.radialMap_val

@[simp]
theorem radialMap_one (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    (hr : (1 : ℝ) ∈ Set.Icc 1 2) : c.radialMap z 1 hr = c.boundaryMap z := by
  apply Subtype.ext
  simp only [radialMap_val, boundaryMap_val, one_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.radialMap_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.radialMap_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.radialMap_one ``Submission.DifferentialGeometry.Topology.BallChart.radialMap_one

theorem isCompact_closedBall_image : IsCompact (c.chart '' Metric.closedBall 0 1) :=
  (_root_.ProperSpace.isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).image_of_continuousOn
    (c.chart.contMDiffOn_toFun.continuousOn.mono c.closedBall_one_subset_source)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.isCompact_closedBall_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.isCompact_closedBall_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.isCompact_closedBall_image ``Submission.DifferentialGeometry.Topology.BallChart.isCompact_closedBall_image

def interior [T2Space M] : TopologicalSpace.Opens M :=
  ⟨(c.chart '' Metric.closedBall 0 1)ᶜ, c.isCompact_closedBall_image.isClosed.isOpen_compl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.interior ``Submission.DifferentialGeometry.Topology.BallChart.interior

@[simp]
theorem mem_interior [T2Space M] {x : M} :
    x ∈ c.interior ↔ x ∉ c.chart '' Metric.closedBall 0 1 := Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.mem_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.mem_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.mem_interior ``Submission.DifferentialGeometry.Topology.BallChart.mem_interior

def interiorToPunctured [T2Space M] (x : c.interior) : c.Punctured :=
  ⟨x, by
    rintro ⟨y, hy, h⟩
    exact x.2 ⟨y, le_of_lt (Metric.mem_ball.mp hy), h⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.interiorToPunctured then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.interiorToPunctured"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.interiorToPunctured ``Submission.DifferentialGeometry.Topology.BallChart.interiorToPunctured

@[simp]
theorem interiorToPunctured_val [T2Space M] (x : c.interior) :
    (c.interiorToPunctured x : M) = x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.interiorToPunctured_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.interiorToPunctured_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.interiorToPunctured_val ``Submission.DifferentialGeometry.Topology.BallChart.interiorToPunctured_val

theorem continuous_interiorToPunctured [T2Space M] : Continuous c.interiorToPunctured :=
  continuous_subtype_val.subtype_mk _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.continuous_interiorToPunctured then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.continuous_interiorToPunctured"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.continuous_interiorToPunctured ``Submission.DifferentialGeometry.Topology.BallChart.continuous_interiorToPunctured

theorem interiorToPunctured_injective [T2Space M] :
    Function.Injective c.interiorToPunctured := by
  intro x y h
  exact Subtype.ext (congrArg (fun z : c.Punctured => (z : M)) h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.interiorToPunctured_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.interiorToPunctured_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.interiorToPunctured_injective ``Submission.DifferentialGeometry.Topology.BallChart.interiorToPunctured_injective

theorem interior_boundary_cover [T2Space M] (x : c.Punctured) :
    (∃ y, c.interiorToPunctured y = x) ∨ (∃ z, c.boundaryMap z = x) := by
  classical
  by_cases hx : (x : M) ∈ c.chart '' Metric.closedBall 0 1
  · obtain ⟨y, hy, heq⟩ := hx
    have hynot : ¬dist y 0 < 1 := by
      intro hylt
      exact x.2 ⟨y, hylt, heq⟩
    have hyone : _root_.Dist.dist y 0 = 1 :=
      le_antisymm (Metric.mem_closedBall.mp hy) (le_of_not_gt hynot)
    exact Or.inr ⟨⟨y, hyone⟩, Subtype.ext heq⟩
  · exact Or.inl ⟨⟨x, hx⟩, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.interior_boundary_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.interior_boundary_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.interior_boundary_cover ``Submission.DifferentialGeometry.Topology.BallChart.interior_boundary_cover

end BallChart

namespace ConnectedSumQuotient

def collarInterval : TopologicalSpace.Opens ℝ :=
  ⟨Set.Ioo (-(1 / 2 : ℝ)) (1 / 2), isOpen_Ioo⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.collarInterval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.collarInterval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.collarInterval ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.collarInterval

abbrev CollarDomain :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × collarInterval

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.CollarDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.CollarDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.CollarDomain ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.CollarDomain

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : Type*} [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
  {N : Type*} [TopologicalSpace N] [ChartedSpace K N]
  (c : BallChart 3 I M) (d : BallChart 3 J N)
  (a : Diffeomorph (𝓡 2) (𝓡 2)
    (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞)

theorem collar_left_radius (t : collarInterval) (ht : 0 ≤ (t : ℝ)) :
    1 + (t : ℝ) ∈ Set.Ico 1 (3 / 2 : ℝ) := by
  have htupper := t.2.2
  constructor <;> linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.collar_left_radius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.collar_left_radius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.collar_left_radius ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.collar_left_radius

theorem collar_right_radius (t : collarInterval) (ht : (t : ℝ) ≤ 0) :
    1 - (t : ℝ) ∈ Set.Ico 1 (3 / 2 : ℝ) := by
  have htlower := t.2.1
  constructor <;> linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.collar_right_radius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.collar_right_radius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.collar_right_radius ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.collar_right_radius

def collarMap (p : CollarDomain) : ConnectedSumQuotient c d a.toHomeomorph :=
  if ht : 0 ≤ (p.2 : ℝ) then
    inl c d a.toHomeomorph (c.radialMap p.1 (1 + (p.2 : ℝ)) (by
      have hr := collar_left_radius p.2 ht
      exact ⟨hr.1, le_trans (le_of_lt hr.2) (by norm_num)⟩))
  else
    inr c d a.toHomeomorph (d.radialMap (a p.1) (1 - (p.2 : ℝ)) (by
      have hr := collar_right_radius p.2 (le_of_lt (lt_of_not_ge ht))
      exact ⟨hr.1, le_trans (le_of_lt hr.2) (by norm_num)⟩))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.collarMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.collarMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.collarMap ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.collarMap

theorem collarMap_of_nonneg (p : CollarDomain) (ht : 0 ≤ (p.2 : ℝ)) :
    collarMap c d a p = inl c d a.toHomeomorph
      (c.radialMap p.1 (1 + (p.2 : ℝ)) (by
        have hr := collar_left_radius p.2 ht
        exact ⟨hr.1, le_trans (le_of_lt hr.2) (by norm_num)⟩)) := by
  simp only [collarMap, dif_pos ht]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.collarMap_of_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.collarMap_of_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.collarMap_of_nonneg ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.collarMap_of_nonneg

theorem collarMap_of_neg (p : CollarDomain) (ht : (p.2 : ℝ) < 0) :
    collarMap c d a p = inr c d a.toHomeomorph
      (d.radialMap (a p.1) (1 - (p.2 : ℝ)) (by
        have hr := collar_right_radius p.2 ht.le
        exact ⟨hr.1, le_trans (le_of_lt hr.2) (by norm_num)⟩)) := by
  simp only [collarMap, dif_neg (not_le.mpr ht)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.collarMap_of_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.collarMap_of_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.collarMap_of_neg ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.collarMap_of_neg

theorem collarMap_zero_left (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    collarMap c d a (z, ⟨0, by constructor <;> norm_num [collarInterval]⟩) =
      inl c d a.toHomeomorph (c.boundaryMap z) := by
  simp [collarMap]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.collarMap_zero_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.collarMap_zero_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.collarMap_zero_left ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.collarMap_zero_left

theorem collarMap_zero_right (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    collarMap c d a (z, ⟨0, by constructor <;> norm_num [collarInterval]⟩) =
      inr c d a.toHomeomorph (d.boundaryMap (a z)) := by
  rw [collarMap_zero_left]
  exact boundary_eq c d a.toHomeomorph z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.collarMap_zero_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.collarMap_zero_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.collarMap_zero_right ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.collarMap_zero_right

def interiorLeft [T2Space M] : c.interior → ConnectedSumQuotient c d a.toHomeomorph :=
  inl c d a.toHomeomorph ∘ c.interiorToPunctured

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.interiorLeft then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.interiorLeft"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.interiorLeft ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.interiorLeft

def interiorRight [T2Space N] : d.interior → ConnectedSumQuotient c d a.toHomeomorph :=
  inr c d a.toHomeomorph ∘ d.interiorToPunctured

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.interiorRight then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.interiorRight"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.interiorRight ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.interiorRight

theorem continuous_interiorLeft [T2Space M] : Continuous (interiorLeft c d a) :=
  (continuous_inl c d a.toHomeomorph).comp c.continuous_interiorToPunctured

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.continuous_interiorLeft then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.continuous_interiorLeft"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.continuous_interiorLeft ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.continuous_interiorLeft

theorem continuous_interiorRight [T2Space N] : Continuous (interiorRight c d a) :=
  (continuous_inr c d a.toHomeomorph).comp d.continuous_interiorToPunctured

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.continuous_interiorRight then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.continuous_interiorRight"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.continuous_interiorRight ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.continuous_interiorRight

theorem interiorLeft_injective [T2Space M] : Function.Injective (interiorLeft c d a) :=
  (inl_injective c d a.toHomeomorph).comp c.interiorToPunctured_injective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.interiorLeft_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.interiorLeft_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.interiorLeft_injective ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.interiorLeft_injective

theorem interiorRight_injective [T2Space N] : Function.Injective (interiorRight c d a) :=
  (inr_injective c d a.toHomeomorph).comp d.interiorToPunctured_injective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.interiorRight_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.interiorRight_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.interiorRight_injective ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.interiorRight_injective

theorem interior_collar_cover [T2Space M] [T2Space N]
    (x : ConnectedSumQuotient c d a.toHomeomorph) :
    (∃ y, interiorLeft c d a y = x) ∨
      (∃ y, interiorRight c d a y = x) ∨ (∃ p, collarMap c d a p = x) := by
  obtain ⟨y, rfl⟩ | ⟨y, rfl⟩ := jointly_surjective c d a.toHomeomorph x
  · obtain ⟨z, rfl⟩ | ⟨z, rfl⟩ := c.interior_boundary_cover y
    · exact Or.inl ⟨z, rfl⟩
    · exact Or.inr (Or.inr ⟨(z, ⟨0, by constructor <;> norm_num [collarInterval]⟩),
        collarMap_zero_left c d a z⟩)
  · obtain ⟨z, rfl⟩ | ⟨z, rfl⟩ := d.interior_boundary_cover y
    · exact Or.inr (Or.inl ⟨z, rfl⟩)
    · refine Or.inr (Or.inr ⟨(a.symm z, ⟨0, by constructor <;> norm_num [collarInterval]⟩), ?_⟩)
      simpa only [a.apply_symm_apply] using collarMap_zero_right c d a (a.symm z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.interior_collar_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.interior_collar_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.interior_collar_cover ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.interior_collar_cover

theorem mem_chart_source_of_norm_le_two {x : EuclideanSpace ℝ (Fin 3)} (hx : ‖x‖ ≤ 2) :
    x ∈ c.chart.source :=
  c.closedBall_subset_source (by simpa [Metric.mem_closedBall, dist_zero_right] using hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.mem_chart_source_of_norm_le_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.mem_chart_source_of_norm_le_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.mem_chart_source_of_norm_le_two ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.mem_chart_source_of_norm_le_two

theorem continuous_radialFamily
    (z : CollarDomain → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (r : CollarDomain → ℝ) (hz : Continuous z) (hr : Continuous r)
    (h1 : ∀ p, 1 ≤ r p) (h2 : ∀ p, r p ≤ 2) :
    Continuous fun p => c.radialMap (z p) (r p) ⟨h1 p, h2 p⟩ := by
  have hsmul : Continuous fun p : CollarDomain =>
      r p • ((z p : EuclideanSpace ℝ (Fin 3))) :=
    hr.smul (continuous_subtype_val.comp hz)
  have hsrc : ∀ p : CollarDomain,
      r p • ((z p : EuclideanSpace ℝ (Fin 3))) ∈ c.chart.source := by
    intro p
    refine mem_chart_source_of_norm_le_two c ?_
    have hz1 : ‖(z p : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using (z p).2
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_trans zero_le_one (h1 p)), hz1, mul_one]
    exact h2 p
  have hchart : Continuous fun p : CollarDomain =>
      (⟨c.chart (r p • ((z p : EuclideanSpace ℝ (Fin 3)))),
        (c.radialMap (z p) (r p) ⟨h1 p, h2 p⟩).2⟩ : c.Punctured) :=
    ((c.chart.contMDiffOn_toFun.continuousOn.comp_continuous hsmul hsrc)).subtype_mk _
  convert hchart using 1
  funext p
  exact Subtype.ext rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.continuous_radialFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.continuous_radialFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.continuous_radialFamily ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.continuous_radialFamily

def radialLeftClamp : CollarDomain → c.Punctured :=
  fun p => c.radialMap p.1 (_root_.Max.max 1 (1 + (p.2 : ℝ))) (by
    refine ⟨le_max_left _ _, max_le (by norm_num) ?_⟩
    have h := p.2.2.2
    linarith)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.radialLeftClamp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.radialLeftClamp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.radialLeftClamp ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.radialLeftClamp

theorem continuous_radialLeftClamp : Continuous (radialLeftClamp c) := by
  have hr : Continuous fun p : CollarDomain => _root_.Max.max 1 (1 + (p.2 : ℝ)) :=
    continuous_const.max (continuous_const.add (continuous_subtype_val.comp continuous_snd))
  refine continuous_radialFamily c (fun p => p.1) (fun p => _root_.Max.max 1 (1 + (p.2 : ℝ)))
    continuous_fst hr ?_ ?_
  · intro p; exact le_max_left _ _
  · intro p
    refine max_le (by norm_num) ?_
    have h := p.2.2.2
    linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.continuous_radialLeftClamp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.continuous_radialLeftClamp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.continuous_radialLeftClamp ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.continuous_radialLeftClamp

theorem radialLeftClamp_of_nonneg (p : CollarDomain) (ht : 0 ≤ (p.2 : ℝ)) :
    radialLeftClamp c p = c.radialMap p.1 (1 + (p.2 : ℝ))
      (by
        have h := collar_left_radius p.2 ht
        exact ⟨h.1, le_trans (le_of_lt h.2) (by norm_num)⟩) := by
  apply Subtype.ext
  change c.chart ((_root_.Max.max 1 (1 + (p.2 : ℝ))) • ((p.1 : EuclideanSpace ℝ (Fin 3)))) =
    c.chart ((1 + (p.2 : ℝ)) • ((p.1 : EuclideanSpace ℝ (Fin 3))))
  rw [max_eq_right (by linarith : (1 : ℝ) ≤ 1 + (p.2 : ℝ))]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.radialLeftClamp_of_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.radialLeftClamp_of_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.radialLeftClamp_of_nonneg ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.radialLeftClamp_of_nonneg

def radialRightClamp (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    CollarDomain → c.Punctured :=
  fun p => c.radialMap z (_root_.Max.max 1 (1 - (p.2 : ℝ))) (by
    refine ⟨le_max_left _ _, max_le (by norm_num) ?_⟩
    have h := p.2.2.1
    linarith)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.radialRightClamp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.radialRightClamp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.radialRightClamp ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.radialRightClamp

theorem continuous_radialRightClamp
    (z : CollarDomain → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (hz : Continuous z) :
    Continuous fun p => radialRightClamp c (z p) p := by
  have hr : Continuous fun p : CollarDomain => _root_.Max.max 1 (1 - (p.2 : ℝ)) :=
    continuous_const.max (continuous_const.sub (continuous_subtype_val.comp continuous_snd))
  refine continuous_radialFamily c z (fun p => _root_.Max.max 1 (1 - (p.2 : ℝ))) hz hr ?_ ?_
  · intro p; exact le_max_left _ _
  · intro p
    refine max_le (by norm_num) ?_
    have h := p.2.2.1
    linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.continuous_radialRightClamp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.continuous_radialRightClamp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.continuous_radialRightClamp ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.continuous_radialRightClamp

theorem radialRightClamp_of_neg (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (p : CollarDomain) (ht : (p.2 : ℝ) < 0) :
    radialRightClamp c z p = c.radialMap z (1 - (p.2 : ℝ))
      (by
        have h := collar_right_radius p.2 ht.le
        exact ⟨h.1, le_trans (le_of_lt h.2) (by norm_num)⟩) := by
  apply Subtype.ext
  change c.chart ((_root_.Max.max 1 (1 - (p.2 : ℝ))) • ((z : EuclideanSpace ℝ (Fin 3)))) =
    c.chart ((1 - (p.2 : ℝ)) • ((z : EuclideanSpace ℝ (Fin 3))))
  rw [max_eq_right (by linarith : (1 : ℝ) ≤ 1 - (p.2 : ℝ))]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.radialRightClamp_of_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.radialRightClamp_of_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.radialRightClamp_of_neg ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.radialRightClamp_of_neg

def collarLeft : CollarDomain → ConnectedSumQuotient c d a.toHomeomorph :=
  fun p => inl c d a.toHomeomorph (radialLeftClamp c p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.collarLeft then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.collarLeft"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.collarLeft ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.collarLeft

def collarRight : CollarDomain → ConnectedSumQuotient c d a.toHomeomorph :=
  fun p => inr c d a.toHomeomorph (radialRightClamp d (a p.1) p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.collarRight then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.collarRight"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.collarRight ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.collarRight

theorem continuous_collarLeft : Continuous (collarLeft c d a) :=
  (continuous_inl c d a.toHomeomorph).comp (continuous_radialLeftClamp c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.continuous_collarLeft then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.continuous_collarLeft"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.continuous_collarLeft ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.continuous_collarLeft

theorem continuous_collarRight : Continuous (collarRight c d a) := by
  have hz : Continuous fun p : CollarDomain => a p.1 :=
    Continuous.comp a.toHomeomorph.continuous_toFun continuous_fst
  exact (continuous_inr c d a.toHomeomorph).comp (continuous_radialRightClamp d _ hz)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.continuous_collarRight then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.continuous_collarRight"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.continuous_collarRight ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.continuous_collarRight

theorem collarLeft_of_nonneg (p : CollarDomain) (ht : 0 ≤ (p.2 : ℝ)) :
    collarLeft c d a p = collarMap c d a p := by
  rw [collarMap_of_nonneg c d a p ht]
  exact congrArg (inl c d a.toHomeomorph) (radialLeftClamp_of_nonneg c p ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.collarLeft_of_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.collarLeft_of_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.collarLeft_of_nonneg ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.collarLeft_of_nonneg

theorem collarRight_of_neg (p : CollarDomain) (ht : (p.2 : ℝ) < 0) :
    collarRight c d a p = collarMap c d a p := by
  rw [collarMap_of_neg c d a p ht]
  exact congrArg (inr c d a.toHomeomorph) (radialRightClamp_of_neg d (a p.1) p ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.collarRight_of_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.collarRight_of_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.collarRight_of_neg ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.collarRight_of_neg

theorem collarLeft_eq_collarRight_of_eq_zero (p : CollarDomain) (ht : (p.2 : ℝ) = 0) :
    collarLeft c d a p = collarRight c d a p := by
  have hleft : radialLeftClamp c p = c.boundaryMap p.1 := by
    apply Subtype.ext
    change c.chart ((_root_.Max.max 1 (1 + (p.2 : ℝ))) • ((p.1 : EuclideanSpace ℝ (Fin 3)))) =
      c.chart ((p.1 : EuclideanSpace ℝ (Fin 3)))
    rw [ht]
    norm_num
  have hright : radialRightClamp d (a p.1) p = d.boundaryMap (a p.1) := by
    apply Subtype.ext
    change d.chart ((_root_.Max.max 1 (1 - (p.2 : ℝ))) •
        (((a p.1 : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
          EuclideanSpace ℝ (Fin 3)))) =
      d.chart (((a p.1 : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
        EuclideanSpace ℝ (Fin 3)))
    rw [ht]
    norm_num
  rw [collarLeft, collarRight, hleft, hright]
  exact boundary_eq c d a.toHomeomorph p.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.collarLeft_eq_collarRight_of_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.collarLeft_eq_collarRight_of_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.collarLeft_eq_collarRight_of_eq_zero ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.collarLeft_eq_collarRight_of_eq_zero

theorem collarMap_eq_if :
    collarMap c d a = fun p : CollarDomain =>
      if 0 ≤ (p.2 : ℝ) then collarLeft c d a p else collarRight c d a p := by
  funext p
  by_cases ht : 0 ≤ (p.2 : ℝ)
  · rw [if_pos ht, ← collarLeft_of_nonneg c d a p ht]
  · rw [if_neg ht, ← collarRight_of_neg c d a p (lt_of_not_ge ht)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.collarMap_eq_if then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.collarMap_eq_if"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.collarMap_eq_if ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.collarMap_eq_if

theorem continuous_collarMap : Continuous (collarMap c d a) := by
  rw [collarMap_eq_if]
  refine continuous_if ?_ (continuous_collarLeft c d a).continuousOn
    (continuous_collarRight c d a).continuousOn
  intro p hp
  exact collarLeft_eq_collarRight_of_eq_zero c d a p
    (frontier_half_le_subset_eq_zero (fun q : CollarDomain => (q.2 : ℝ))
      (continuous_subtype_val.comp continuous_snd) hp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.continuous_collarMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.continuous_collarMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.continuous_collarMap ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.continuous_collarMap

end ConnectedSumQuotient

end DifferentialGeometry.Topology
