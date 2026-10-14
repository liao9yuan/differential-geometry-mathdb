import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Quotient
import Submission.DifferentialGeometry.Topology.Manifold.Attachment.AdjunctionSeparation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology

namespace BallChart

variable {n : ℕ} {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] (c d : BallChart n I M)

abbrev DoublePunctured :=
  ↥((c.chart '' Metric.ball 0 1 ∪ d.chart '' Metric.ball 0 1)ᶜ : Set M)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.DoublePunctured then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.DoublePunctured"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.DoublePunctured ``Submission.DifferentialGeometry.Topology.BallChart.DoublePunctured

theorem isClosed_doublePunctured :
    IsClosed ((c.chart '' Metric.ball 0 1 ∪ d.chart '' Metric.ball 0 1)ᶜ : Set M) :=
  (c.isOpen_chart_image_ball.union d.isOpen_chart_image_ball).isClosed_compl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.isClosed_doublePunctured then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.isClosed_doublePunctured"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.isClosed_doublePunctured ``Submission.DifferentialGeometry.Topology.BallChart.isClosed_doublePunctured

instance instCompactSpaceDoublePunctured [CompactSpace M] :
    CompactSpace (c.DoublePunctured d) :=
  isCompact_iff_compactSpace.mp (c.isClosed_doublePunctured d).isCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.instCompactSpaceDoublePunctured then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.instCompactSpaceDoublePunctured"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.instCompactSpaceDoublePunctured ``Submission.DifferentialGeometry.Topology.BallChart.instCompactSpaceDoublePunctured

variable (hdisj : Disjoint (c.chart '' Metric.closedBall 0 2)
  (d.chart '' Metric.closedBall 0 2))

include hdisj in
theorem chart_sphere_not_mem_other_ball
    (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    c.chart z ∉ d.chart '' Metric.ball 0 1 := by
  intro hz
  exact Set.disjoint_left.mp hdisj
    ⟨z, by rw [Metric.mem_closedBall, Metric.mem_sphere.mp z.2]; norm_num, rfl⟩
    (Set.image_mono (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall
      (by norm_num : (1 : ℝ) ≤ 2))) hz)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.chart_sphere_not_mem_other_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.chart_sphere_not_mem_other_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.chart_sphere_not_mem_other_ball ``Submission.DifferentialGeometry.Topology.BallChart.chart_sphere_not_mem_other_ball

def firstBoundaryMap (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    c.DoublePunctured d :=
  ⟨c.chart z, fun h => h.elim (c.boundaryMap z).property
    (c.chart_sphere_not_mem_other_ball d hdisj z)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.firstBoundaryMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.firstBoundaryMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.firstBoundaryMap ``Submission.DifferentialGeometry.Topology.BallChart.firstBoundaryMap

def secondBoundaryMap (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    c.DoublePunctured d :=
  ⟨d.chart z, fun h => h.elim (d.chart_sphere_not_mem_other_ball c hdisj.symm z)
    (d.boundaryMap z).property⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.secondBoundaryMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.secondBoundaryMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.secondBoundaryMap ``Submission.DifferentialGeometry.Topology.BallChart.secondBoundaryMap

@[simp] theorem firstBoundaryMap_val
    (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    (c.firstBoundaryMap d hdisj z).val = c.chart z := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.firstBoundaryMap_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.firstBoundaryMap_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.firstBoundaryMap_val ``Submission.DifferentialGeometry.Topology.BallChart.firstBoundaryMap_val

@[simp] theorem secondBoundaryMap_val
    (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    (c.secondBoundaryMap d hdisj z).val = d.chart z := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.secondBoundaryMap_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.secondBoundaryMap_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.secondBoundaryMap_val ``Submission.DifferentialGeometry.Topology.BallChart.secondBoundaryMap_val

theorem firstBoundaryMap_injective : _root_.Function.Injective (c.firstBoundaryMap d hdisj) := by
  intro z w h
  exact Subtype.ext (c.chart.toPartialEquiv.injOn (c.sphere_subset_source z.2)
    (c.sphere_subset_source w.2) (congrArg Subtype.val h))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.firstBoundaryMap_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.firstBoundaryMap_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.firstBoundaryMap_injective ``Submission.DifferentialGeometry.Topology.BallChart.firstBoundaryMap_injective

theorem secondBoundaryMap_injective : _root_.Function.Injective (c.secondBoundaryMap d hdisj) := by
  intro z w h
  exact Subtype.ext (d.chart.toPartialEquiv.injOn (d.sphere_subset_source z.2)
    (d.sphere_subset_source w.2) (congrArg Subtype.val h))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.secondBoundaryMap_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.secondBoundaryMap_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.secondBoundaryMap_injective ``Submission.DifferentialGeometry.Topology.BallChart.secondBoundaryMap_injective

theorem firstBoundaryMap_ne_secondBoundaryMap
    (z w : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    c.firstBoundaryMap d hdisj z ≠ c.secondBoundaryMap d hdisj w := by
  intro h
  have heq : c.chart z = d.chart w := congrArg Subtype.val h
  exact Set.disjoint_left.mp hdisj
    ⟨z, by rw [Metric.mem_closedBall, Metric.mem_sphere.mp z.2]; norm_num, rfl⟩
    ⟨w, by rw [Metric.mem_closedBall, Metric.mem_sphere.mp w.2]; norm_num, heq.symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.firstBoundaryMap_ne_secondBoundaryMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.firstBoundaryMap_ne_secondBoundaryMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.firstBoundaryMap_ne_secondBoundaryMap ``Submission.DifferentialGeometry.Topology.BallChart.firstBoundaryMap_ne_secondBoundaryMap

theorem continuous_firstBoundaryMap : Continuous (c.firstBoundaryMap d hdisj) :=
  (c.chart.contMDiffOn_toFun.continuousOn.comp_continuous
    continuous_subtype_val (fun z => c.sphere_subset_source z.2)).subtype_mk _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.continuous_firstBoundaryMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.continuous_firstBoundaryMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.continuous_firstBoundaryMap ``Submission.DifferentialGeometry.Topology.BallChart.continuous_firstBoundaryMap

theorem continuous_secondBoundaryMap : Continuous (c.secondBoundaryMap d hdisj) :=
  (d.chart.contMDiffOn_toFun.continuousOn.comp_continuous
    continuous_subtype_val (fun z => d.sphere_subset_source z.2)).subtype_mk _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.continuous_secondBoundaryMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.continuous_secondBoundaryMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.continuous_secondBoundaryMap ``Submission.DifferentialGeometry.Topology.BallChart.continuous_secondBoundaryMap

end BallChart

namespace SelfAttachment

variable {n : ℕ}

abbrev Sphere := Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.Sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.Sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.Sphere ``Submission.DifferentialGeometry.Topology.SelfAttachment.Sphere
abbrev Band := Sphere (n := n) × _root_.Set.Icc (0 : ℝ) 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.Band then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.Band"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.Band ``Submission.DifferentialGeometry.Topology.SelfAttachment.Band

def boundaryInclusion : Bool × Sphere (n := n) → Band (n := n)
  | (_root_.Bool.false, z) => (z, ⟨0, by norm_num⟩)
  | (_root_.Bool.true, z) => (z, ⟨1, by norm_num⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.boundaryInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.boundaryInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.boundaryInclusion ``Submission.DifferentialGeometry.Topology.SelfAttachment.boundaryInclusion

theorem boundaryInclusion_injective : _root_.Function.Injective (boundaryInclusion (n := n)) := by
  rintro ⟨b, z⟩ ⟨e, w⟩ h
  cases b <;> cases e
  · exact Prod.ext rfl (congrArg Prod.fst h)
  · have ht := congrArg (fun q : Band (n := n) => q.2.val) h
    norm_num [boundaryInclusion] at ht
  · have ht := congrArg (fun q : Band (n := n) => q.2.val) h
    norm_num [boundaryInclusion] at ht
  · exact Prod.ext rfl (congrArg Prod.fst h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.boundaryInclusion_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.boundaryInclusion_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.boundaryInclusion_injective ``Submission.DifferentialGeometry.Topology.SelfAttachment.boundaryInclusion_injective

theorem continuous_boundaryInclusion : Continuous (boundaryInclusion (n := n)) := by
  apply continuous_prod_of_discrete_left.mpr
  intro b
  cases b <;> exact continuous_id.prodMk continuous_const

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.continuous_boundaryInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.continuous_boundaryInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.continuous_boundaryInclusion ``Submission.DifferentialGeometry.Topology.SelfAttachment.continuous_boundaryInclusion

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] (c d : BallChart n I M)
  (hdisj : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))
  (a : Sphere (n := n) ≃ₜ Sphere (n := n))

def attachingMap : Bool × Sphere (n := n) → c.DoublePunctured d
  | (_root_.Bool.false, z) => c.firstBoundaryMap d hdisj z
  | (_root_.Bool.true, z) => c.secondBoundaryMap d hdisj (a z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.attachingMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.attachingMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.attachingMap ``Submission.DifferentialGeometry.Topology.SelfAttachment.attachingMap

theorem attachingMap_injective : _root_.Function.Injective (attachingMap c d hdisj a) := by
  rintro ⟨b, z⟩ ⟨e, w⟩ h
  cases b <;> cases e
  · exact Prod.ext rfl (c.firstBoundaryMap_injective d hdisj h)
  · exact False.elim (c.firstBoundaryMap_ne_secondBoundaryMap d hdisj z (a w) h)
  · exact False.elim (c.firstBoundaryMap_ne_secondBoundaryMap d hdisj w (a z) h.symm)
  · exact Prod.ext rfl (a.injective (c.secondBoundaryMap_injective d hdisj h))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.attachingMap_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.attachingMap_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.attachingMap_injective ``Submission.DifferentialGeometry.Topology.SelfAttachment.attachingMap_injective

theorem continuous_attachingMap : Continuous (attachingMap c d hdisj a) := by
  apply continuous_prod_of_discrete_left.mpr
  intro b
  cases b
  · exact c.continuous_firstBoundaryMap d hdisj
  · exact (c.continuous_secondBoundaryMap d hdisj).comp a.continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.continuous_attachingMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.continuous_attachingMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.continuous_attachingMap ``Submission.DifferentialGeometry.Topology.SelfAttachment.continuous_attachingMap

abbrev Quotient := AdjunctionSpace (boundaryInclusion (n := n)) (attachingMap c d hdisj a)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.Quotient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.Quotient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.Quotient ``Submission.DifferentialGeometry.Topology.SelfAttachment.Quotient

def coreInclusion : c.DoublePunctured d → Quotient c d hdisj a :=
  adjunctionLower (i := boundaryInclusion) (attachingMap c d hdisj a)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.coreInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.coreInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.coreInclusion ``Submission.DifferentialGeometry.Topology.SelfAttachment.coreInclusion

def bandInclusion : Band (n := n) → Quotient c d hdisj a :=
  adjunctionCell boundaryInclusion (attachingMap c d hdisj a)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.bandInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.bandInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.bandInclusion ``Submission.DifferentialGeometry.Topology.SelfAttachment.bandInclusion

theorem seam_eq (q : Bool × Sphere (n := n)) :
    bandInclusion c d hdisj a (boundaryInclusion q) =
      coreInclusion c d hdisj a (attachingMap c d hdisj a q) :=
  adjunction_coherence _ _ q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.seam_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.seam_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.seam_eq ``Submission.DifferentialGeometry.Topology.SelfAttachment.seam_eq

theorem continuous_coreInclusion : Continuous (coreInclusion c d hdisj a) :=
  continuous_adjunctionLower _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.continuous_coreInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.continuous_coreInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.continuous_coreInclusion ``Submission.DifferentialGeometry.Topology.SelfAttachment.continuous_coreInclusion

theorem continuous_bandInclusion : Continuous (bandInclusion c d hdisj a) :=
  continuous_adjunctionCell _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.continuous_bandInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.continuous_bandInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.continuous_bandInclusion ``Submission.DifferentialGeometry.Topology.SelfAttachment.continuous_bandInclusion

theorem coreInclusion_injective : _root_.Function.Injective (coreInclusion c d hdisj a) :=
  Manifold.Attachment.adjunctionLower_injective _ _ boundaryInclusion_injective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.coreInclusion_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.coreInclusion_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.coreInclusion_injective ``Submission.DifferentialGeometry.Topology.SelfAttachment.coreInclusion_injective

theorem bandInclusion_injective : _root_.Function.Injective (bandInclusion c d hdisj a) :=
  Manifold.Attachment.adjunctionCell_injective _ _ boundaryInclusion_injective
    (attachingMap_injective c d hdisj a)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.bandInclusion_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.bandInclusion_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.bandInclusion_injective ``Submission.DifferentialGeometry.Topology.SelfAttachment.bandInclusion_injective

theorem bandInclusion_eq_coreInclusion_iff (q : Band (n := n)) (x : c.DoublePunctured d) :
    bandInclusion c d hdisj a q = coreInclusion c d hdisj a x ↔
      ∃ z, boundaryInclusion z = q ∧ attachingMap c d hdisj a z = x :=
  Manifold.Attachment.adjunctionCell_eq_lower_iff _ _ boundaryInclusion_injective q x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.bandInclusion_eq_coreInclusion_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.bandInclusion_eq_coreInclusion_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.bandInclusion_eq_coreInclusion_iff ``Submission.DifferentialGeometry.Topology.SelfAttachment.bandInclusion_eq_coreInclusion_iff

theorem inclusions_cover :
    range (bandInclusion c d hdisj a) ∪ _root_.Set.range (coreInclusion c d hdisj a) = univ :=
  Manifold.Attachment.adjunction_inclusions_cover _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.inclusions_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.inclusions_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.inclusions_cover ``Submission.DifferentialGeometry.Topology.SelfAttachment.inclusions_cover

theorem inclusions_inter :
    _root_.Set.range (bandInclusion c d hdisj a) ∩ _root_.Set.range (coreInclusion c d hdisj a) =
      range (bandInclusion c d hdisj a ∘ boundaryInclusion) :=
  Manifold.Attachment.adjunction_inclusions_inter _ _ boundaryInclusion_injective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.inclusions_inter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.inclusions_inter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.inclusions_inter ``Submission.DifferentialGeometry.Topology.SelfAttachment.inclusions_inter

instance instT2Space [T2Space M] : T2Space (Quotient c d hdisj a) :=
  Manifold.Attachment.adjunction_t2Space _ _ boundaryInclusion_injective
    (attachingMap_injective c d hdisj a) continuous_boundaryInclusion
    (continuous_attachingMap c d hdisj a)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.instT2Space then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.instT2Space"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.instT2Space ``Submission.DifferentialGeometry.Topology.SelfAttachment.instT2Space

instance instCompactSpace [CompactSpace M] : CompactSpace (Quotient c d hdisj a) :=
  _root_.Quot.compactSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.instCompactSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.instCompactSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.instCompactSpace ``Submission.DifferentialGeometry.Topology.SelfAttachment.instCompactSpace

theorem isClosedEmbedding_coreInclusion [T2Space M] :
    _root_.Topology.IsClosedEmbedding (coreInclusion c d hdisj a) :=
  Manifold.Attachment.isClosedEmbedding_adjunctionLower _ _ boundaryInclusion_injective
    (attachingMap_injective c d hdisj a) continuous_boundaryInclusion
    (continuous_attachingMap c d hdisj a)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.isClosedEmbedding_coreInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.isClosedEmbedding_coreInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.isClosedEmbedding_coreInclusion ``Submission.DifferentialGeometry.Topology.SelfAttachment.isClosedEmbedding_coreInclusion

theorem isClosedEmbedding_bandInclusion [T2Space M] :
    _root_.Topology.IsClosedEmbedding (bandInclusion c d hdisj a) :=
  Manifold.Attachment.isClosedEmbedding_adjunctionCell _ _ boundaryInclusion_injective
    (attachingMap_injective c d hdisj a) continuous_boundaryInclusion
    (continuous_attachingMap c d hdisj a)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.isClosedEmbedding_bandInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.isClosedEmbedding_bandInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.isClosedEmbedding_bandInclusion ``Submission.DifferentialGeometry.Topology.SelfAttachment.isClosedEmbedding_bandInclusion

end SelfAttachment
end DifferentialGeometry.Topology
