import Submission.DifferentialGeometry.Topology.ThreeManifold.PairedBallMerge

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section

open _root_.Set _root_.Metric _root_.Submission.Metric

namespace DifferentialGeometry.Topology.ConnectedSumQuotient

universe u v
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ConnectedSumQuotient.E3 target :: scope.openDecls } }

variable {M : ConnectedClosedOrientedManifold.{u} 3}
  {N : ConnectedClosedOrientedManifold.{v} 3}
  (c : OrientedBallChart M.toClosedOrientedManifold)
  (d : OrientedBallChart N.toClosedOrientedManifold) (a : BoundaryAttachment)
  {L R : Type*}
  (e : L → OrientedBallChart M.toClosedOrientedManifold)
  (f : R → OrientedBallChart N.toClosedOrientedManifold)
  (b : L ⊕ R → OrientedBallChart
    (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.toClosedOrientedManifold)
  (hbL : ∀ i x, x ∈ closedBall (0 : E3) 2 →
    ∃ hx : (e i).chart x ∉ c.chart '' ball (0 : E3) 1,
      (b (Sum.inl i)).chart x = inl c.toBallChart d.toBallChart a.1.toHomeomorph ⟨(e i).chart x, hx⟩)
  (hbR : ∀ i x, x ∈ closedBall (0 : E3) 2 →
    ∃ hx : (f i).chart x ∉ d.chart '' ball (0 : E3) 1,
      (b (Sum.inr i)).chart x = inr c.toBallChart d.toBallChart a.1.toHomeomorph ⟨(f i).chart x, hx⟩)

include hbL hbR in
theorem inl_mem_surviving_image_iff_of_avoids_boundary
    (hfd : ∀ i x, x ∈ _root_.Metric.closedBall (0 : E3) 2 →
      (f i).chart x ∉ d.chart '' _root_.Metric.closedBall (0 : E3) 1)
    (S : Set E3) (hS : S ⊆ _root_.Metric.closedBall (0 : E3) 2) (x : c.Punctured) :
    inl c.toBallChart d.toBallChart a.1.toHomeomorph x ∈ ⋃ i, (b i).chart '' S ↔
      x.val ∈ ⋃ i, (e i).chart '' S := by
  constructor
  · intro h
    obtain ⟨i,z,hz,hzx⟩ := mem_iUnion.mp h
    cases i with
    | inl i =>
      obtain ⟨hzi,ht⟩ := hbL i z (hS hz)
      rw [ht] at hzx
      exact mem_iUnion.mpr ⟨i,z,hz,congrArg Subtype.val
        (inl_injective c.toBallChart d.toBallChart a.1.toHomeomorph hzx)⟩
    | inr i =>
      obtain ⟨hzi,ht⟩ := hbR i z (hS hz)
      rw [ht] at hzx
      obtain ⟨w,_,hw⟩ := (inl_eq_inr_iff c.toBallChart d.toBallChart a.1.toHomeomorph _ _).mp hzx.symm
      exact False.elim (hfd i z (hS hz)
        ⟨a.1 w,_root_.Metric.sphere_subset_closedBall (a.1 w).property,congrArg Subtype.val hw⟩)
  · intro h
    obtain ⟨i,z,hz,hzx⟩ := mem_iUnion.mp h
    obtain ⟨hzi,ht⟩ := hbL i z (hS hz)
    exact mem_iUnion.mpr ⟨Sum.inl i,z,hz,ht.trans
      (congrArg (inl c.toBallChart d.toBallChart a.1.toHomeomorph) (Subtype.ext hzx))⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.inl_mem_surviving_image_iff_of_avoids_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.inl_mem_surviving_image_iff_of_avoids_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.inl_mem_surviving_image_iff_of_avoids_boundary ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.inl_mem_surviving_image_iff_of_avoids_boundary

include hbL hbR in
theorem inr_mem_surviving_image_iff_of_avoids_boundary
    (hec : ∀ i x, x ∈ _root_.Metric.closedBall (0 : E3) 2 →
      (e i).chart x ∉ c.chart '' _root_.Metric.closedBall (0 : E3) 1)
    (S : Set E3) (hS : S ⊆ _root_.Metric.closedBall (0 : E3) 2) (x : d.Punctured) :
    inr c.toBallChart d.toBallChart a.1.toHomeomorph x ∈ ⋃ i, (b i).chart '' S ↔
      x.val ∈ ⋃ i, (f i).chart '' S := by
  constructor
  · intro h
    obtain ⟨i,z,hz,hzx⟩ := mem_iUnion.mp h
    cases i with
    | inr i =>
      obtain ⟨hzi,ht⟩ := hbR i z (hS hz)
      rw [ht] at hzx
      exact mem_iUnion.mpr ⟨i,z,hz,congrArg Subtype.val
        (inr_injective c.toBallChart d.toBallChart a.1.toHomeomorph hzx)⟩
    | inl i =>
      obtain ⟨hzi,ht⟩ := hbL i z (hS hz)
      rw [ht] at hzx
      obtain ⟨w,hw,_⟩ := (inl_eq_inr_iff c.toBallChart d.toBallChart a.1.toHomeomorph _ _).mp hzx
      exact False.elim (hec i z (hS hz)
        ⟨w,_root_.Metric.sphere_subset_closedBall w.property,congrArg Subtype.val hw⟩)
  · intro h
    obtain ⟨i,z,hz,hzx⟩ := mem_iUnion.mp h
    obtain ⟨hzi,ht⟩ := hbR i z (hS hz)
    exact mem_iUnion.mpr ⟨Sum.inr i,z,hz,ht.trans
      (congrArg (inr c.toBallChart d.toBallChart a.1.toHomeomorph) (Subtype.ext hzx))⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.inr_mem_surviving_image_iff_of_avoids_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.inr_mem_surviving_image_iff_of_avoids_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.inr_mem_surviving_image_iff_of_avoids_boundary ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.inr_mem_surviving_image_iff_of_avoids_boundary

end DifferentialGeometry.Topology.ConnectedSumQuotient

end

end

section

noncomputable section

open _root_.Set _root_.Metric _root_.Submission.Metric
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.ConnectedSumQuotient

universe u v

variable {M : ConnectedClosedOrientedManifold.{u} 3}
  {N : ConnectedClosedOrientedManifold.{v} 3}
  (c : OrientedBallChart M.toClosedOrientedManifold)
  (d : OrientedBallChart N.toClosedOrientedManifold) (a : BoundaryAttachment)
  {L R : Type*}
  (e : L → OrientedBallChart M.toClosedOrientedManifold)
  (f : R → OrientedBallChart N.toClosedOrientedManifold)
  (b : L ⊕ R → OrientedBallChart
    (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.toClosedOrientedManifold)
  (hbL : ∀ i x, x ∈ closedBall (0 : E3) 2 →
    ∃ hx : (e i).chart x ∉ c.chart '' ball (0 : E3) 1,
      (b (Sum.inl i)).chart x = inl c.toBallChart d.toBallChart a.1.toHomeomorph ⟨(e i).chart x, hx⟩)
  (hbR : ∀ i x, x ∈ closedBall (0 : E3) 2 →
    ∃ hx : (f i).chart x ∉ d.chart '' ball (0 : E3) 1,
      (b (Sum.inr i)).chart x = inr c.toBallChart d.toBallChart a.1.toHomeomorph ⟨(f i).chart x, hx⟩)
  (hec : ∀ i, Disjoint ((e i).chart '' closedBall (0 : E3) 2) (c.chart '' closedBall (0 : E3) 2))
  (hfd : ∀ i, Disjoint ((f i).chart '' closedBall (0 : E3) 2) (d.chart '' closedBall (0 : E3) 2))

include hbL hbR hec hfd in
theorem collarMap_not_mem_surviving_closed_balls (p : CollarDomain) :
    collarMap c.toBallChart d.toBallChart a.1 p ∉ ⋃ i, (b i).chart '' _root_.Metric.closedBall (0 : E3) 1 := by
  have he (i : L) (x : E3) (hx : x ∈ _root_.Metric.closedBall (0 : E3) 2) :
      (e i).chart x ∉ c.chart '' _root_.Metric.closedBall (0 : E3) 1 :=
    fun h => disjoint_left.mp (hec i) ⟨x,hx,rfl⟩
      (_root_.Set.image_mono (_root_.Metric.closedBall_subset_closedBall (by norm_num)) h)
  have hf (i : R) (x : E3) (hx : x ∈ _root_.Metric.closedBall (0 : E3) 2) :
      (f i).chart x ∉ d.chart '' _root_.Metric.closedBall (0 : E3) 1 :=
    fun h => disjoint_left.mp (hfd i) ⟨x,hx,rfl⟩
      (_root_.Set.image_mono (_root_.Metric.closedBall_subset_closedBall (by norm_num)) h)
  by_cases ht : 0 ≤ (p.2 : ℝ)
  · rw [collarMap_of_nonneg _ _ _ p ht,
      inl_mem_surviving_image_iff_of_avoids_boundary c d a e f b hbL hbR hf _
        (_root_.Metric.closedBall_subset_closedBall (by norm_num))]
    intro h
    obtain ⟨i,z,hz,hzq⟩ := mem_iUnion.mp h
    apply disjoint_left.mp (hec i)
      ⟨z,_root_.Metric.closedBall_subset_closedBall (by norm_num) hz,hzq⟩
    refine ⟨(1 + (p.2 : ℝ)) • (p.1 : E3), ?_, rfl⟩
    rw [_root_.Metric.mem_closedBall,dist_zero_right,BallChart.norm_radial p.1 (by linarith)]
    exact (collar_left_radius p.2 ht).2.le.trans (by norm_num)
  · have htt := lt_of_not_ge ht
    rw [collarMap_of_neg _ _ _ p htt,
      inr_mem_surviving_image_iff_of_avoids_boundary c d a e f b hbL hbR he _
        (_root_.Metric.closedBall_subset_closedBall (by norm_num))]
    intro h
    obtain ⟨i,z,hz,hzq⟩ := mem_iUnion.mp h
    apply disjoint_left.mp (hfd i)
      ⟨z,_root_.Metric.closedBall_subset_closedBall (by norm_num) hz,hzq⟩
    refine ⟨(1 - (p.2 : ℝ)) • ((a.1 p.1) : E3), ?_, rfl⟩
    rw [_root_.Metric.mem_closedBall,dist_zero_right,BallChart.norm_radial (a.1 p.1) (by linarith)]
    exact (collar_right_radius p.2 htt.le).2.le.trans (by norm_num)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.collarMap_not_mem_surviving_closed_balls then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.collarMap_not_mem_surviving_closed_balls"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.collarMap_not_mem_surviving_closed_balls ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.collarMap_not_mem_surviving_closed_balls

variable [Finite L] [Finite R]

include hbL hbR hec hfd in
theorem collarMap_mem_interior_surviving_complement (p : CollarDomain) :
    collarMap c.toBallChart d.toBallChart a.1 p ∈
      interior (⋃ i, (b i).chart '' _root_.Metric.ball (0 : E3) 1)ᶜ := by
  have hopen : IsOpen (⋃ i, (b i).chart '' _root_.Metric.closedBall (0 : E3) 1)ᶜ :=
    (isClosed_iUnion_of_finite (fun i => (b i).isCompact_closedBall_image.isClosed)).isOpen_compl
  apply mem_interior.mpr
  refine ⟨(⋃ i, (b i).chart '' _root_.Metric.closedBall (0 : E3) 1)ᶜ, ?_, hopen,
    collarMap_not_mem_surviving_closed_balls c d a e f b hbL hbR hec hfd p⟩
  intro x hx h
  obtain ⟨i,z,hz,hzx⟩ := mem_iUnion.mp h
  exact hx (mem_iUnion.mpr ⟨i,z,_root_.Metric.ball_subset_closedBall hz,hzx⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.collarMap_mem_interior_surviving_complement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.collarMap_mem_interior_surviving_complement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.collarMap_mem_interior_surviving_complement ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.collarMap_mem_interior_surviving_complement

end DifferentialGeometry.Topology.ConnectedSumQuotient

end

end
