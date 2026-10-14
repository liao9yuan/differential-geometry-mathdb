import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientedFactorBallChart

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Metric _root_.Submission.Metric
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

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

private theorem image_chart_subset_transport_left
    (e : OrientedBallChart M.toClosedOrientedManifold)
    (e' : OrientedBallChart
      (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.toClosedOrientedManifold)
    (he : ∀ x ∈ _root_.Metric.closedBall (0 : E3) 2,
      ∃ hx : e.chart x ∉ c.chart '' _root_.Metric.ball (0 : E3) 1,
        e'.chart x = inl c.toBallChart d.toBallChart a.1.toHomeomorph ⟨e.chart x, hx⟩)
    (S : Set E3) (hS : S ⊆ _root_.Metric.closedBall (0 : E3) 2) :
    (inl c.toBallChart d.toBallChart a.1.toHomeomorph) ⁻¹' (e'.chart '' S) =
      {x : c.Punctured | x.val ∈ e.chart '' S} := by
  ext x
  constructor
  · rintro ⟨w, hw, hweq⟩
    obtain ⟨_, htransport⟩ := he w (hS hw)
    rw [htransport] at hweq
    exact ⟨w, hw, congrArg Subtype.val ((inl_injective c.toBallChart d.toBallChart
      a.1.toHomeomorph) hweq)⟩
  · rintro ⟨w, hw, hweq⟩
    obtain ⟨hw', htransport⟩ := he w (hS hw)
    exact ⟨w, hw, htransport.trans (congrArg
      (inl c.toBallChart d.toBallChart a.1.toHomeomorph) (Subtype.ext hweq))⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.image_chart_subset_transport_left
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ConnectedSumQuotient.image_chart_subset_transport_left target :: scope.openDecls } }

private theorem image_chart_subset_transport_right
    (e : OrientedBallChart N.toClosedOrientedManifold)
    (e' : OrientedBallChart
      (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.toClosedOrientedManifold)
    (he : ∀ x ∈ _root_.Metric.closedBall (0 : E3) 2,
      ∃ hx : e.chart x ∉ d.chart '' _root_.Metric.ball (0 : E3) 1,
        e'.chart x = inr c.toBallChart d.toBallChart a.1.toHomeomorph ⟨e.chart x, hx⟩)
    (S : Set E3) (hS : S ⊆ _root_.Metric.closedBall (0 : E3) 2) :
    (inr c.toBallChart d.toBallChart a.1.toHomeomorph) ⁻¹' (e'.chart '' S) =
      {x : d.Punctured | x.val ∈ e.chart '' S} := by
  ext x
  constructor
  · rintro ⟨w, hw, hweq⟩
    obtain ⟨_, htransport⟩ := he w (hS hw)
    rw [htransport] at hweq
    exact ⟨w, hw, congrArg Subtype.val ((inr_injective c.toBallChart d.toBallChart
      a.1.toHomeomorph) hweq)⟩
  · rintro ⟨w, hw, hweq⟩
    obtain ⟨hw', htransport⟩ := he w (hS hw)
    exact ⟨w, hw, htransport.trans (congrArg
      (inr c.toBallChart d.toBallChart a.1.toHomeomorph) (Subtype.ext hweq))⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.image_chart_subset_transport_right
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ConnectedSumQuotient.image_chart_subset_transport_right target :: scope.openDecls } }

private theorem inr_preimage_left_chart_subset_empty
    (e : OrientedBallChart M.toClosedOrientedManifold)
    (e' : OrientedBallChart
      (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.toClosedOrientedManifold)
    (hdisj : ∀ x ∈ _root_.Metric.closedBall (0 : E3) 2,
      e.chart x ∉ c.chart '' _root_.Metric.closedBall (0 : E3) 1)
    (he : ∀ x ∈ _root_.Metric.closedBall (0 : E3) 2,
      ∃ hx : e.chart x ∉ c.chart '' _root_.Metric.ball (0 : E3) 1,
        e'.chart x = inl c.toBallChart d.toBallChart a.1.toHomeomorph ⟨e.chart x, hx⟩)
    (S : Set E3) (hS : S ⊆ _root_.Metric.closedBall (0 : E3) 2) :
    (inr c.toBallChart d.toBallChart a.1.toHomeomorph) ⁻¹' (e'.chart '' S) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro y
  rintro ⟨w, hw, hweq⟩
  obtain ⟨_, htransport⟩ := he w (hS hw)
  rw [htransport] at hweq
  obtain ⟨z, hz, _⟩ :=
    (inl_eq_inr_iff c.toBallChart d.toBallChart a.1.toHomeomorph _ _).mp hweq
  exact hdisj w (hS hw)
    ⟨z, _root_.Metric.sphere_subset_closedBall z.property, congrArg Subtype.val hz⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.inr_preimage_left_chart_subset_empty
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ConnectedSumQuotient.inr_preimage_left_chart_subset_empty target :: scope.openDecls } }

private theorem inl_preimage_right_chart_subset_empty
    (e : OrientedBallChart N.toClosedOrientedManifold)
    (e' : OrientedBallChart
      (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.toClosedOrientedManifold)
    (hdisj : ∀ x ∈ _root_.Metric.closedBall (0 : E3) 2,
      e.chart x ∉ d.chart '' _root_.Metric.closedBall (0 : E3) 1)
    (he : ∀ x ∈ _root_.Metric.closedBall (0 : E3) 2,
      ∃ hx : e.chart x ∉ d.chart '' _root_.Metric.ball (0 : E3) 1,
        e'.chart x = inr c.toBallChart d.toBallChart a.1.toHomeomorph ⟨e.chart x, hx⟩)
    (S : Set E3) (hS : S ⊆ _root_.Metric.closedBall (0 : E3) 2) :
    (inl c.toBallChart d.toBallChart a.1.toHomeomorph) ⁻¹' (e'.chart '' S) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro y
  rintro ⟨w, hw, hweq⟩
  obtain ⟨_, htransport⟩ := he w (hS hw)
  rw [htransport] at hweq
  obtain ⟨z, _, hz⟩ :=
    (inl_eq_inr_iff c.toBallChart d.toBallChart a.1.toHomeomorph _ _).mp hweq.symm
  exact hdisj w (hS hw)
    ⟨a.1 z, _root_.Metric.sphere_subset_closedBall (a.1 z).property, congrArg Subtype.val hz⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.inl_preimage_right_chart_subset_empty
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ConnectedSumQuotient.inl_preimage_right_chart_subset_empty target :: scope.openDecls } }

theorem preimage_inl_chart_image_ball
    (e : OrientedBallChart M.toClosedOrientedManifold)
    (e' : OrientedBallChart
      (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.toClosedOrientedManifold)
    (he : ∀ x ∈ _root_.Metric.closedBall (0 : E3) 2,
      ∃ hx : e.chart x ∉ c.chart '' _root_.Metric.ball (0 : E3) 1,
        e'.chart x = inl c.toBallChart d.toBallChart a.1.toHomeomorph ⟨e.chart x, hx⟩) :
    (inl c.toBallChart d.toBallChart a.1.toHomeomorph) ⁻¹'
        (e'.chart '' _root_.Metric.ball (0 : E3) 1) =
      {x : c.Punctured | x.val ∈ e.chart '' _root_.Metric.ball (0 : E3) 1} :=
  image_chart_subset_transport_left c d a e e' he _
    (ball_subset_closedBall.trans (_root_.Metric.closedBall_subset_closedBall (by norm_num)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.preimage_inl_chart_image_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.preimage_inl_chart_image_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.preimage_inl_chart_image_ball ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.preimage_inl_chart_image_ball

theorem preimage_inr_chart_image_ball_of_eq_inl
    (e : OrientedBallChart M.toClosedOrientedManifold)
    (e' : OrientedBallChart
      (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.toClosedOrientedManifold)
    (hdisj : ∀ x ∈ _root_.Metric.closedBall (0 : E3) 2,
      e.chart x ∉ c.chart '' _root_.Metric.closedBall (0 : E3) 1)
    (he : ∀ x ∈ _root_.Metric.closedBall (0 : E3) 2,
      ∃ hx : e.chart x ∉ c.chart '' _root_.Metric.ball (0 : E3) 1,
        e'.chart x = inl c.toBallChart d.toBallChart a.1.toHomeomorph ⟨e.chart x, hx⟩) :
    (inr c.toBallChart d.toBallChart a.1.toHomeomorph) ⁻¹'
        (e'.chart '' _root_.Metric.ball (0 : E3) 1) = ∅ :=
  inr_preimage_left_chart_subset_empty c d a e e' hdisj he _
    (ball_subset_closedBall.trans (_root_.Metric.closedBall_subset_closedBall (by norm_num)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.preimage_inr_chart_image_ball_of_eq_inl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.preimage_inr_chart_image_ball_of_eq_inl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.preimage_inr_chart_image_ball_of_eq_inl ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.preimage_inr_chart_image_ball_of_eq_inl

theorem exists_orientedBallChart_inl_preimage
    (e : OrientedBallChart M.toClosedOrientedManifold)
    (hdisj : ∀ x ∈ _root_.Metric.closedBall (0 : E3) 2,
      e.chart x ∉ c.chart '' _root_.Metric.closedBall (0 : E3) 1) :
    ∃ e' : OrientedBallChart
        (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.toClosedOrientedManifold,
      (∀ x ∈ _root_.Metric.closedBall (0 : E3) 2,
        ∃ hx : e.chart x ∉ c.chart '' _root_.Metric.ball (0 : E3) 1,
          e'.chart x = inl c.toBallChart d.toBallChart a.1.toHomeomorph ⟨e.chart x, hx⟩) ∧
      (inl c.toBallChart d.toBallChart a.1.toHomeomorph) ⁻¹'
          (e'.chart '' _root_.Metric.ball (0 : E3) 1) =
        {x : c.Punctured | x.val ∈ e.chart '' _root_.Metric.ball (0 : E3) 1} ∧
      (inr c.toBallChart d.toBallChart a.1.toHomeomorph) ⁻¹'
          (e'.chart '' _root_.Metric.ball (0 : E3) 1) = ∅ := by
  obtain ⟨e', he'⟩ := exists_orientedBallChart_inl c d a e hdisj
  exact ⟨e', he', preimage_inl_chart_image_ball c d a e e' he',
    preimage_inr_chart_image_ball_of_eq_inl c d a e e' hdisj he'⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.exists_orientedBallChart_inl_preimage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.exists_orientedBallChart_inl_preimage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.exists_orientedBallChart_inl_preimage ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.exists_orientedBallChart_inl_preimage

theorem exists_orientedBallChart_family_inl_preimage {ι : Type*}
    (e : ι → OrientedBallChart M.toClosedOrientedManifold)
    (hdisj : ∀ i x, x ∈ _root_.Metric.closedBall (0 : E3) 2 →
      (e i).chart x ∉ c.chart '' _root_.Metric.closedBall (0 : E3) 1) :
    ∃ e' : ι → OrientedBallChart
        (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.toClosedOrientedManifold,
      (∀ i x, x ∈ _root_.Metric.closedBall (0 : E3) 2 →
        ∃ hx : (e i).chart x ∉ c.chart '' _root_.Metric.ball (0 : E3) 1,
          (e' i).chart x = inl c.toBallChart d.toBallChart a.1.toHomeomorph
            ⟨(e i).chart x, hx⟩) ∧
      (inl c.toBallChart d.toBallChart a.1.toHomeomorph) ⁻¹'
          (⋃ i, (e' i).chart '' _root_.Metric.ball (0 : E3) 1) =
        {x : c.Punctured | x.val ∈ ⋃ i, (e i).chart '' _root_.Metric.ball (0 : E3) 1} ∧
      (inr c.toBallChart d.toBallChart a.1.toHomeomorph) ⁻¹'
          (⋃ i, (e' i).chart '' _root_.Metric.ball (0 : E3) 1) = ∅ := by
  choose e' he' hleft hright using
    fun i => exists_orientedBallChart_inl_preimage c d a (e i) (hdisj i)
  refine ⟨e', he', ?_, ?_⟩
  · ext x
    simp only [_root_.Set.mem_preimage, _root_.Set.mem_iUnion, _root_.Set.mem_ofPred_eq]
    exact exists_congr fun i => Set.ext_iff.mp (hleft i) x
  · rw [_root_.Set.preimage_iUnion]
    simp only [hright, _root_.Set.iUnion_empty]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.exists_orientedBallChart_family_inl_preimage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.exists_orientedBallChart_family_inl_preimage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.exists_orientedBallChart_family_inl_preimage ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.exists_orientedBallChart_family_inl_preimage

theorem exists_orientedBallChart_sum_family_preimage {ι κ : Type*}
    (e : ι → OrientedBallChart M.toClosedOrientedManifold)
    (f : κ → OrientedBallChart N.toClosedOrientedManifold)
    (hec : ∀ i x, x ∈ _root_.Metric.closedBall (0 : E3) 2 →
      (e i).chart x ∉ c.chart '' _root_.Metric.closedBall (0 : E3) 1)
    (hfd : ∀ i x, x ∈ _root_.Metric.closedBall (0 : E3) 2 →
      (f i).chart x ∉ d.chart '' _root_.Metric.closedBall (0 : E3) 1)
    (he : Pairwise fun i j => Disjoint ((e i).chart '' _root_.Metric.closedBall (0 : E3) 2)
      ((e j).chart '' _root_.Metric.closedBall (0 : E3) 2))
    (hf : Pairwise fun i j => Disjoint ((f i).chart '' _root_.Metric.closedBall (0 : E3) 2)
      ((f j).chart '' _root_.Metric.closedBall (0 : E3) 2)) :
    ∃ b : ι ⊕ κ → OrientedBallChart
        (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.toClosedOrientedManifold,
      (∀ i x, x ∈ _root_.Metric.closedBall (0 : E3) 2 →
        ∃ hx : (e i).chart x ∉ c.chart '' _root_.Metric.ball (0 : E3) 1,
          (b (Sum.inl i)).chart x = inl c.toBallChart d.toBallChart a.1.toHomeomorph
            ⟨(e i).chart x, hx⟩) ∧
      (∀ i x, x ∈ _root_.Metric.closedBall (0 : E3) 2 →
        ∃ hx : (f i).chart x ∉ d.chart '' _root_.Metric.ball (0 : E3) 1,
          (b (Sum.inr i)).chart x = inr c.toBallChart d.toBallChart a.1.toHomeomorph
            ⟨(f i).chart x, hx⟩) ∧
      (Pairwise fun i j => Disjoint ((b i).chart '' _root_.Metric.closedBall (0 : E3) 2)
        ((b j).chart '' _root_.Metric.closedBall (0 : E3) 2)) ∧
      (∀ (S : Set E3), S ⊆ _root_.Metric.closedBall (0 : E3) 2 →
        (inl c.toBallChart d.toBallChart a.1.toHomeomorph) ⁻¹'
            (⋃ i, (b i).chart '' S) =
          {x : c.Punctured | x.val ∈ ⋃ i, (e i).chart '' S}) ∧
      (∀ (S : Set E3), S ⊆ _root_.Metric.closedBall (0 : E3) 2 →
        (inr c.toBallChart d.toBallChart a.1.toHomeomorph) ⁻¹'
            (⋃ i, (b i).chart '' S) =
          {x : d.Punctured | x.val ∈ ⋃ i, (f i).chart '' S}) := by
  classical
  choose e' he' using fun i => exists_orientedBallChart_inl c d a (e i) (hec i)
  choose f' hf' using fun i => exists_orientedBallChart_inr c d a (f i) (hfd i)
  let b := Sum.elim e' f'
  have hLL (S : Set E3) (hS : S ⊆ _root_.Metric.closedBall (0 : E3) 2) (i : ι) :=
    image_chart_subset_transport_left c d a (e i) (e' i) (he' i) S hS
  have hRR (S : Set E3) (hS : S ⊆ _root_.Metric.closedBall (0 : E3) 2) (i : κ) :=
    image_chart_subset_transport_right c d a (f i) (f' i) (hf' i) S hS
  have hRL (S : Set E3) (hS : S ⊆ _root_.Metric.closedBall (0 : E3) 2) (i : ι) :=
    inr_preimage_left_chart_subset_empty c d a (e i) (e' i) (hec i) (he' i) S hS
  have hLR (S : Set E3) (hS : S ⊆ _root_.Metric.closedBall (0 : E3) 2) (i : κ) :=
    inl_preimage_right_chart_subset_empty c d a (f i) (f' i) (hfd i) (hf' i) S hS
  refine ⟨b, he', hf', ?_, ?_, ?_⟩
  · intro i j hij
    rw [Set.disjoint_left]
    intro z hz hz'
    rcases i with i | i <;> rcases j with j | j
    · obtain ⟨x, hx, rfl⟩ := hz
      obtain ⟨hx', hxeq⟩ := he' i x hx
      have hzj : inl c.toBallChart d.toBallChart a.1.toHomeomorph ⟨(e i).chart x, hx'⟩ ∈
          (e' j).chart '' _root_.Metric.closedBall (0 : E3) 2 := by rwa [← hxeq]
      have hmem := Set.ext_iff.mp (hLL _ subset_rfl j) ⟨(e i).chart x, hx'⟩
      exact Set.disjoint_left.mp (he (fun h => hij (congrArg Sum.inl h)))
        ⟨x, hx, rfl⟩ (hmem.mp hzj)
    · obtain ⟨x, hx, rfl⟩ := hz
      obtain ⟨hx', hxeq⟩ := he' i x hx
      have hzj : inl c.toBallChart d.toBallChart a.1.toHomeomorph ⟨(e i).chart x, hx'⟩ ∈
          (f' j).chart '' _root_.Metric.closedBall (0 : E3) 2 := by rwa [← hxeq]
      have hmem := Set.ext_iff.mp (hLR _ subset_rfl j) ⟨(e i).chart x, hx'⟩
      exact hmem.mp hzj
    · obtain ⟨x, hx, rfl⟩ := hz
      obtain ⟨hx', hxeq⟩ := hf' i x hx
      have hzj : inr c.toBallChart d.toBallChart a.1.toHomeomorph ⟨(f i).chart x, hx'⟩ ∈
          (e' j).chart '' _root_.Metric.closedBall (0 : E3) 2 := by rwa [← hxeq]
      have hmem := Set.ext_iff.mp (hRL _ subset_rfl j) ⟨(f i).chart x, hx'⟩
      exact hmem.mp hzj
    · obtain ⟨x, hx, rfl⟩ := hz
      obtain ⟨hx', hxeq⟩ := hf' i x hx
      have hzj : inr c.toBallChart d.toBallChart a.1.toHomeomorph ⟨(f i).chart x, hx'⟩ ∈
          (f' j).chart '' _root_.Metric.closedBall (0 : E3) 2 := by rwa [← hxeq]
      have hmem := Set.ext_iff.mp (hRR _ subset_rfl j) ⟨(f i).chart x, hx'⟩
      exact Set.disjoint_left.mp (hf (fun h => hij (congrArg Sum.inr h)))
        ⟨x, hx, rfl⟩ (hmem.mp hzj)
  · intro S hS
    ext x
    simp only [_root_.Set.mem_preimage, _root_.Set.mem_iUnion, Sum.exists, _root_.Set.mem_ofPred_eq]
    constructor
    · rintro (⟨i, hi⟩ | ⟨j, hj⟩)
      · exact ⟨i, (Set.ext_iff.mp (hLL S hS i) x).mp hi⟩
      · exact ((Set.ext_iff.mp (hLR S hS j) x).mp hj).elim
    · rintro ⟨i, hi⟩
      exact Or.inl ⟨i, (Set.ext_iff.mp (hLL S hS i) x).mpr hi⟩
  · intro S hS
    ext x
    simp only [_root_.Set.mem_preimage, _root_.Set.mem_iUnion, Sum.exists, _root_.Set.mem_ofPred_eq]
    constructor
    · rintro (⟨i, hi⟩ | ⟨j, hj⟩)
      · exact ((Set.ext_iff.mp (hRL S hS i) x).mp hi).elim
      · exact ⟨j, (Set.ext_iff.mp (hRR S hS j) x).mp hj⟩
    · rintro ⟨j, hj⟩
      exact Or.inr ⟨j, (Set.ext_iff.mp (hRR S hS j) x).mpr hj⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.exists_orientedBallChart_sum_family_preimage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.exists_orientedBallChart_sum_family_preimage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.exists_orientedBallChart_sum_family_preimage ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.exists_orientedBallChart_sum_family_preimage

end DifferentialGeometry.Topology.ConnectedSumQuotient
