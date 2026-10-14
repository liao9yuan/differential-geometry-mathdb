import Submission.DifferentialGeometry.Topology.Embedding.FiniteDimension
import Submission.DifferentialGeometry.Topology.Embedding.SliceChart
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Connected.Clopen
import Mathlib.SetTheory.Cardinal.Finite

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Metric _root_.Topology
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

private theorem exists_compl_sides_of_slice_chart
    {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Φ : OpenPartialHomeomorph X (E × ℝ)) {K : Set X}
    (hK : Φ '' (Φ.source ∩ K) = Φ.target ∩ (_root_.Set.univ ×ˢ ({0} : Set ℝ)))
    {x : X} (hx : x ∈ Φ.source ∩ K) :
    ∃ U V W : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ Φ.source ∧
      IsOpen V ∧ IsOpen W ∧ IsConnected V ∧ IsConnected W ∧
      Disjoint V W ∧ V ∪ W = U \ K ∧ U ∩ K ⊆ frontier V ∩ frontier W := by
  have hslice : ∀ y ∈ Φ.source, y ∈ K ↔ (Φ y).2 = 0 := by
    intro y hy
    constructor
    · intro hyK
      have hm : Φ y ∈ Φ '' (Φ.source ∩ K) := ⟨y, ⟨hy, hyK⟩, rfl⟩
      rw [hK] at hm
      exact hm.2.2
    · intro hy0
      have hm : Φ y ∈ Φ '' (Φ.source ∩ K) := by
        rw [hK]
        exact ⟨Φ.map_source hy, _root_.Set.mem_univ _, hy0⟩
      obtain ⟨z, hz, hzy⟩ := hm
      exact Φ.injOn hz.1 hy hzy ▸ hz.2
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp Φ.open_target _ (Φ.map_source hx.1)
  let B : Set (E × ℝ) := _root_.Metric.ball (Φ x).1 r ×ˢ _root_.Set.Ioo (-r) r
  let P : Set (E × ℝ) := _root_.Metric.ball (Φ x).1 r ×ˢ _root_.Set.Ioo 0 r
  let Q : Set (E × ℝ) := _root_.Metric.ball (Φ x).1 r ×ˢ _root_.Set.Ioo (-r) 0
  have hcenter : ((Φ x).1, 0) = Φ x := Prod.ext rfl ((hslice x hx.1).mp hx.2).symm
  have hB : B ⊆ Φ.target := by
    intro q hq
    apply hball
    rw [← hcenter, ← ball_prod_same, Real.ball_zero_eq_Ioo]
    exact hq
  have hPB : P ⊆ B := by
    rintro q ⟨hq, hp, hpr⟩
    exact ⟨hq, by linarith, hpr⟩
  have hQB : Q ⊆ B := by
    rintro q ⟨hq, hqr, hn⟩
    exact ⟨hq, hqr, by linarith⟩
  have hP : P ⊆ Φ.target := hPB.trans hB
  have hQ : Q ⊆ Φ.target := hQB.trans hB
  let U := Φ.symm '' B
  let V := Φ.symm '' P
  let W := Φ.symm '' Q
  have hmem {S : Set (E × ℝ)} (hS : S ⊆ Φ.target) (y : X) :
      y ∈ Φ.symm '' S ↔ y ∈ Φ.source ∧ Φ y ∈ S := by
    exact Iff.of_eq (congrArg (fun S : Set X => y ∈ S)
      (Φ.symm_image_eq_source_inter_preimage hS))
  have hUopen : IsOpen U := Φ.isOpen_image_symm_of_subset_target
    (isOpen_ball.prod isOpen_Ioo) hB
  have hVopen : IsOpen V := Φ.isOpen_image_symm_of_subset_target
    (isOpen_ball.prod isOpen_Ioo) hP
  have hWopen : IsOpen W := Φ.isOpen_image_symm_of_subset_target
    (isOpen_ball.prod isOpen_Ioo) hQ
  have hVconn : IsConnected V := ((_root_.Metric.isConnected_ball hr).prod (isConnected_Ioo hr)).image
    Φ.symm (Φ.symm.continuousOn.mono hP)
  have hWconn : IsConnected W :=
    ((_root_.Metric.isConnected_ball hr).prod (isConnected_Ioo (neg_lt_zero.mpr hr))).image
      Φ.symm (Φ.symm.continuousOn.mono hQ)
  have hdisj : Disjoint V W := by
    rw [_root_.Set.disjoint_left]
    intro y hyV hyW
    have hp := ((hmem hP y).mp hyV).2.2.1
    have hn := ((hmem hQ y).mp hyW).2.2.2
    exact (lt_trans hp hn).false
  have hunion : V ∪ W = U \ K := by
    ext y
    constructor
    · rintro (hy | hy)
      · obtain ⟨hys, hyp⟩ := (hmem hP y).mp hy
        refine ⟨(hmem hB y).mpr ⟨hys, hPB hyp⟩, ?_⟩
        intro hyK
        exact hyp.2.1.ne' ((hslice y hys).mp hyK)
      · obtain ⟨hys, hyq⟩ := (hmem hQ y).mp hy
        refine ⟨(hmem hB y).mpr ⟨hys, hQB hyq⟩, ?_⟩
        intro hyK
        exact hyq.2.2.ne ((hslice y hys).mp hyK)
    · rintro ⟨hyU, hyK⟩
      obtain ⟨hys, hyb⟩ := (hmem hB y).mp hyU
      have hy0 : (Φ y).2 ≠ 0 := fun h => hyK ((hslice y hys).mpr h)
      rcases lt_or_gt_of_ne hy0 with hn | hp
      · exact Or.inr ((hmem hQ y).mpr ⟨hys, hyb.1, hyb.2.1, hn⟩)
      · exact Or.inl ((hmem hP y).mpr ⟨hys, hyb.1, hp, hyb.2.2⟩)
  have hfrontier : U ∩ K ⊆ frontier V ∩ frontier W := by
    rintro y ⟨hyU, hyK⟩
    obtain ⟨hys, hyb⟩ := (hmem hB y).mp hyU
    have hy0 : (Φ y).2 = 0 := (hslice y hys).mp hyK
    have hyP : Φ y ∈ closure P := by
      rw [closure_prod_eq, closure_Ioo hr.ne]
      refine ⟨subset_closure hyb.1, ?_⟩
      change 0 ≤ (Φ y).2 ∧ (Φ y).2 ≤ r
      rw [hy0]
      exact ⟨le_rfl, hr.le⟩
    have hyQ : Φ y ∈ closure Q := by
      rw [closure_prod_eq, closure_Ioo (neg_lt_zero.mpr hr).ne]
      refine ⟨subset_closure hyb.1, ?_⟩
      change -r ≤ (Φ y).2 ∧ (Φ y).2 ≤ 0
      rw [hy0]
      exact ⟨neg_nonpos.mpr hr.le, le_rfl⟩
    have hyV : y ∈ closure V := by
      simpa only [Φ.left_inv hys] using
        ((Φ.symm.continuousOn _ (Φ.map_source hys)).mono hP).mem_closure_image hyP
    have hyW : y ∈ closure W := by
      simpa only [Φ.left_inv hys] using
        ((Φ.symm.continuousOn _ (Φ.map_source hys)).mono hQ).mem_closure_image hyQ
    have hyVnot : y ∉ V := by
      intro hy
      exact ((hmem hP y).mp hy).2.2.1.ne' hy0
    have hyWnot : y ∉ W := by
      intro hy
      exact ((hmem hQ y).mp hy).2.2.2.ne hy0
    rw [frontier, frontier, hVopen.interior_eq, hWopen.interior_eq]
    exact ⟨⟨hyV, hyVnot⟩, hyW, hyWnot⟩
  refine ⟨U, V, W, hUopen, ?_, ?_, hVopen, hWopen, hVconn, hWconn,
    hdisj, hunion, hfrontier⟩
  · apply (hmem hB x).mpr
    refine ⟨hx.1, _root_.Metric.mem_ball_self hr, ?_⟩
    rw [(hslice x hx.1).mp hx.2]
    exact ⟨neg_lt_zero.mpr hr, hr⟩
  · intro y hy
    exact ((hmem hB y).mp hy).1

run_cmd do
  let target := ``Submission.exists_compl_sides_of_slice_chart
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `exists_compl_sides_of_slice_chart target :: scope.openDecls } }

open _root_.Manifold _root_.Manifold.IsSmoothEmbedding in
theorem Manifold.IsSmoothEmbedding.exists_isOpen_isConnected_compl_sides
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V G}
    [I.Boundaryless] [J.Boundaryless]
    {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace G N] {n : ℕ∞ω} {f : M → N}
    (hf : Manifold.IsSmoothEmbedding I J n f)
    (hdim : Module.finrank ℝ E + 1 = Module.finrank ℝ V) (x : M) :
    ∃ U P Q : Set N, IsOpen U ∧ f x ∈ U ∧
      IsOpen P ∧ IsOpen Q ∧ IsConnected P ∧ IsConnected Q ∧
      Disjoint P Q ∧ P ∪ Q = U \ _root_.Set.range f ∧
      U ∩ _root_.Set.range f ⊆ frontier P ∩ frontier Q := by
  have hcodim : Module.finrank ℝ ℝ = Module.finrank ℝ V - Module.finrank ℝ E := by
    simp only [Module.finrank_self]
    omega
  have hi := hf.isImmersion.isImmersionOfComplement_of_finrank_eq hcodim x
  obtain ⟨Φ, hx, _, _, hΦ⟩ :=
    hi.exists_contMDiffOn_slice_chart hf.isEmbedding.isInducing
  rw [I.range_eq_univ] at hΦ
  obtain ⟨U, P, Q, hU, hxU, _, hP, hQ, hPc, hQc, hd, hu, hf⟩ :=
    exists_compl_sides_of_slice_chart Φ hΦ ⟨hx, _root_.Set.mem_range_self x⟩
  exact ⟨U, P, Q, hU, hxU, hP, hQ, hPc, hQc, hd, hu, hf⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.IsSmoothEmbedding.exists_isOpen_isConnected_compl_sides then
    throwError "Refusing to shadow existing declaration Manifold.IsSmoothEmbedding.exists_isOpen_isConnected_compl_sides"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.IsSmoothEmbedding.exists_isOpen_isConnected_compl_sides ``Submission.Manifold.IsSmoothEmbedding.exists_isOpen_isConnected_compl_sides

open _root_.Manifold _root_.Manifold.IsSmoothEmbedding in
theorem Manifold.IsSmoothEmbedding.isOpen_preimage_frontier_connectedComponentIn_compl
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V G}
    [I.Boundaryless] [J.Boundaryless]
    {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace G N] {n : ℕ∞ω} {f : M → N}
    (hf : Manifold.IsSmoothEmbedding I J n f)
    (hdim : Module.finrank ℝ E + 1 = Module.finrank ℝ V) (y : N) :
    IsOpen (f ⁻¹' frontier (connectedComponentIn (_root_.Set.range f)ᶜ y)) := by
  refine isOpen_iff_mem_nhds.mpr fun x hx => ?_
  obtain ⟨U, P, Q, hU, hxU, _, _, hPc, hQc, _, hu, hb⟩ :=
    hf.exists_isOpen_isConnected_compl_sides hdim x
  obtain ⟨z, hzU, hzC⟩ := mem_closure_iff.mp hx.1 U hU hxU
  have hPC : P ⊆ (_root_.Set.range f)ᶜ := by
    intro p hp
    have hm : p ∈ U \ _root_.Set.range f := by
      rw [← hu]
      exact Or.inl hp
    exact hm.2
  have hQC : Q ⊆ (_root_.Set.range f)ᶜ := by
    intro q hq
    have hm : q ∈ U \ _root_.Set.range f := by
      rw [← hu]
      exact Or.inr hq
    exact hm.2
  have hside : P ⊆ connectedComponentIn (_root_.Set.range f)ᶜ y ∨
      Q ⊆ connectedComponentIn (_root_.Set.range f)ᶜ y := by
    have hz : z ∈ P ∪ Q := by
      rw [hu]
      exact ⟨hzU, connectedComponentIn_subset (_root_.Set.range f)ᶜ y hzC⟩
    rcases hz with hzP | hzQ
    · exact Or.inl (by
        rw [connectedComponentIn_eq hzC]
        exact hPc.isPreconnected.subset_connectedComponentIn hzP hPC)
    · exact Or.inr (by
        rw [connectedComponentIn_eq hzC]
        exact hQc.isPreconnected.subset_connectedComponentIn hzQ hQC)
  refine mem_nhds_iff.mpr ⟨f ⁻¹' U, ?_, hU.preimage hf.isEmbedding.continuous, hxU⟩
  intro x' hx'
  have hboundary := hb ⟨hx', _root_.Set.mem_range_self x'⟩
  refine ⟨?_, ?_⟩
  · rcases hside with hP | hQ
    · exact closure_mono hP hboundary.1.1
    · exact closure_mono hQ hboundary.2.1
  · intro h
    exact connectedComponentIn_subset (_root_.Set.range f)ᶜ y (interior_subset h) (_root_.Set.mem_range_self x')

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.IsSmoothEmbedding.isOpen_preimage_frontier_connectedComponentIn_compl then
    throwError "Refusing to shadow existing declaration Manifold.IsSmoothEmbedding.isOpen_preimage_frontier_connectedComponentIn_compl"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.IsSmoothEmbedding.isOpen_preimage_frontier_connectedComponentIn_compl ``Submission.Manifold.IsSmoothEmbedding.isOpen_preimage_frontier_connectedComponentIn_compl

open _root_.IsClosed in
private theorem IsClosed.frontier_connectedComponentIn_compl_subset
    {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]
    {K : Set X} (hK : IsClosed K) (x : X) :
    frontier (connectedComponentIn Kᶜ x) ⊆ K := by
  have hCopen : IsOpen (connectedComponentIn Kᶜ x) :=
    hK.isOpen_compl.connectedComponentIn
  intro z hz
  by_contra hzK
  have hzD : z ∈ connectedComponentIn Kᶜ z := mem_connectedComponentIn hzK
  obtain ⟨w, hwD, hwC⟩ := mem_closure_iff.mp hz.1 (connectedComponentIn Kᶜ z)
    hK.isOpen_compl.connectedComponentIn hzD
  have hCD : connectedComponentIn Kᶜ x = connectedComponentIn Kᶜ z :=
    (connectedComponentIn_eq hwC).trans (connectedComponentIn_eq hwD).symm
  apply hz.2
  rw [hCopen.interior_eq, hCD]
  exact hzD

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.IsClosed
  let target := ``Submission.IsClosed.frontier_connectedComponentIn_compl_subset
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `IsClosed.frontier_connectedComponentIn_compl_subset target :: scope.openDecls } }

private theorem connectedComponents_eq_of_connectedComponentIn_eq
    {X : Type*} [TopologicalSpace X] {S : Set X} {x y : S}
    (h : connectedComponentIn S x = connectedComponentIn S y) :
    ConnectedComponents.mk x = ConnectedComponents.mk y := by
  apply ConnectedComponents.coe_eq_coe.mpr
  apply (image_injective.mpr Subtype.val_injective)
  simpa only [connectedComponentIn_eq_image x.property,
    connectedComponentIn_eq_image y.property] using h

run_cmd do
  let target := ``Submission.connectedComponents_eq_of_connectedComponentIn_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `connectedComponents_eq_of_connectedComponentIn_eq target :: scope.openDecls } }

namespace Manifold
open _root_.Manifold

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V G}
  [I.Boundaryless] [J.Boundaryless]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N] [ConnectedSpace M] [PreconnectedSpace N]
  {n : ℕ∞ω} {f : M → N}

open _root_.Manifold _root_.Manifold.IsSmoothEmbedding in
theorem IsSmoothEmbedding.frontier_connectedComponentIn_compl_range_of_isClosed
    (hf : _root_.Manifold.IsSmoothEmbedding I J n f)
    (hdim : Module.finrank ℝ E + 1 = Module.finrank ℝ V)
    (hclosed : IsClosed (_root_.Set.range f)) {y : N} (hy : y ∈ (_root_.Set.range f)ᶜ) :
    frontier (connectedComponentIn (_root_.Set.range f)ᶜ y) = _root_.Set.range f := by
  let : LocallyConnectedSpace G := J.toHomeomorph.locallyConnectedSpace
  let : LocallyConnectedSpace N := ChartedSpace.locallyConnectedSpace G N
  have hsub := hclosed.frontier_connectedComponentIn_compl_subset y
  have hproper : connectedComponentIn (_root_.Set.range f)ᶜ y ≠ univ := by
    intro h
    obtain ⟨x⟩ := (inferInstance : Nonempty M)
    have hx : f x ∈ connectedComponentIn (_root_.Set.range f)ᶜ y := by rw [h]; trivial
    exact connectedComponentIn_subset (_root_.Set.range f)ᶜ y hx (_root_.Set.mem_range_self x)
  obtain ⟨z, hz⟩ := nonempty_frontier_iff.mpr
    ⟨⟨y, mem_connectedComponentIn hy⟩, hproper⟩
  obtain ⟨x, hx⟩ := hsub hz
  have hclopen : IsClopen (f ⁻¹' frontier (connectedComponentIn (_root_.Set.range f)ᶜ y)) :=
    ⟨isClosed_frontier.preimage hf.isEmbedding.continuous,
      hf.isOpen_preimage_frontier_connectedComponentIn_compl hdim y⟩
  have hall : f ⁻¹' frontier (connectedComponentIn (_root_.Set.range f)ᶜ y) = univ :=
    hclopen.eq_univ ⟨x, by change f x ∈ frontier _; rwa [hx]⟩
  refine hsub.antisymm ?_
  rintro z ⟨x, rfl⟩
  have hm : x ∈ f ⁻¹' frontier (connectedComponentIn (_root_.Set.range f)ᶜ y) := by
    rw [hall]
    trivial
  exact hm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.IsSmoothEmbedding.frontier_connectedComponentIn_compl_range_of_isClosed then
    throwError "Refusing to shadow existing declaration Manifold.IsSmoothEmbedding.frontier_connectedComponentIn_compl_range_of_isClosed"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.IsSmoothEmbedding.frontier_connectedComponentIn_compl_range_of_isClosed ``Submission.Manifold.IsSmoothEmbedding.frontier_connectedComponentIn_compl_range_of_isClosed

open _root_.Manifold _root_.Manifold.IsSmoothEmbedding in
theorem IsSmoothEmbedding.frontier_connectedComponentIn_compl_range_of_compact
    [CompactSpace M] [T2Space N] (hf : _root_.Manifold.IsSmoothEmbedding I J n f)
    (hdim : Module.finrank ℝ E + 1 = Module.finrank ℝ V)
    {y : N} (hy : y ∈ (_root_.Set.range f)ᶜ) :
    frontier (connectedComponentIn (_root_.Set.range f)ᶜ y) = _root_.Set.range f :=
  hf.frontier_connectedComponentIn_compl_range_of_isClosed hdim
    (isCompact_range hf.isEmbedding.continuous).isClosed hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.IsSmoothEmbedding.frontier_connectedComponentIn_compl_range_of_compact then
    throwError "Refusing to shadow existing declaration Manifold.IsSmoothEmbedding.frontier_connectedComponentIn_compl_range_of_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.IsSmoothEmbedding.frontier_connectedComponentIn_compl_range_of_compact ``Submission.Manifold.IsSmoothEmbedding.frontier_connectedComponentIn_compl_range_of_compact

open _root_.Manifold _root_.Manifold.IsSmoothEmbedding in
theorem IsSmoothEmbedding.card_connectedComponents_compl_le_two_of_isClosed
    (hf : _root_.Manifold.IsSmoothEmbedding I J n f)
    (hdim : Module.finrank ℝ E + 1 = Module.finrank ℝ V)
    (hclosed : IsClosed (_root_.Set.range f)) :
    ENat.card (ConnectedComponents ↥((_root_.Set.range f)ᶜ)) ≤ 2 := by
  classical
  obtain ⟨x⟩ := (inferInstance : Nonempty M)
  obtain ⟨U, P, Q, hU, hxU, _, _, hPc, hQc, _, hu, _⟩ :=
    hf.exists_isOpen_isConnected_compl_sides hdim x
  have hPC : P ⊆ (_root_.Set.range f)ᶜ := by
    intro p hp
    have hm : p ∈ U \ _root_.Set.range f := by
      rw [← hu]
      exact Or.inl hp
    exact hm.2
  have hQC : Q ⊆ (_root_.Set.range f)ᶜ := by
    intro q hq
    have hm : q ∈ U \ _root_.Set.range f := by
      rw [← hu]
      exact Or.inr hq
    exact hm.2
  obtain ⟨p, hp⟩ := hPc.nonempty
  obtain ⟨q, hq⟩ := hQc.nonempty
  let p' : ↥((_root_.Set.range f)ᶜ) := ⟨p, hPC hp⟩
  let q' : ↥((_root_.Set.range f)ᶜ) := ⟨q, hQC hq⟩
  have hcover : ∀ c : ConnectedComponents ↥((_root_.Set.range f)ᶜ),
      c = ConnectedComponents.mk p' ∨ c = ConnectedComponents.mk q' := by
    intro c
    obtain ⟨w, rfl⟩ := ConnectedComponents.surjective_coe c
    have hxC : f x ∈ frontier (connectedComponentIn (_root_.Set.range f)ᶜ w.val) := by
      rw [hf.frontier_connectedComponentIn_compl_range_of_isClosed hdim hclosed w.property]
      exact _root_.Set.mem_range_self x
    obtain ⟨z, hzU, hzC⟩ := mem_closure_iff.mp hxC.1 U hU hxU
    have hz : z ∈ P ∪ Q := by
      rw [hu]
      exact ⟨hzU, connectedComponentIn_subset (_root_.Set.range f)ᶜ w.val hzC⟩
    rcases hz with hzP | hzQ
    · have hsub : P ⊆ connectedComponentIn (_root_.Set.range f)ᶜ w.val := by
        rw [connectedComponentIn_eq hzC]
        exact hPc.isPreconnected.subset_connectedComponentIn hzP hPC
      exact Or.inl (connectedComponents_eq_of_connectedComponentIn_eq
        (connectedComponentIn_eq (hsub hp)))
    · have hsub : Q ⊆ connectedComponentIn (_root_.Set.range f)ᶜ w.val := by
        rw [connectedComponentIn_eq hzC]
        exact hQc.isPreconnected.subset_connectedComponentIn hzQ hQC
      exact Or.inr (connectedComponents_eq_of_connectedComponentIn_eq
        (connectedComponentIn_eq (hsub hq)))
  let g : ConnectedComponents ↥((_root_.Set.range f)ᶜ) → Bool :=
    fun c => _root_.Decidable.decide (c = ConnectedComponents.mk p')
  have hg : Function.Injective g := by
    intro a b hab
    rcases hcover a with rfl | rfl <;> rcases hcover b with rfl | rfl
    · rfl
    · exact ((decide_eq_decide.mp hab).mp rfl).symm
    · exact (decide_eq_decide.mp hab).mpr rfl
    · rfl
  calc
    ENat.card (ConnectedComponents ↥((_root_.Set.range f)ᶜ)) ≤ ENat.card Bool :=
      ENat.card_le_card_of_injective hg
    _ = 2 := by simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.IsSmoothEmbedding.card_connectedComponents_compl_le_two_of_isClosed then
    throwError "Refusing to shadow existing declaration Manifold.IsSmoothEmbedding.card_connectedComponents_compl_le_two_of_isClosed"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.IsSmoothEmbedding.card_connectedComponents_compl_le_two_of_isClosed ``Submission.Manifold.IsSmoothEmbedding.card_connectedComponents_compl_le_two_of_isClosed

open _root_.Manifold _root_.Manifold.IsSmoothEmbedding in
theorem IsSmoothEmbedding.card_connectedComponents_compl_le_two_of_compact
    [CompactSpace M] [T2Space N] (hf : _root_.Manifold.IsSmoothEmbedding I J n f)
    (hdim : Module.finrank ℝ E + 1 = Module.finrank ℝ V) :
    ENat.card (ConnectedComponents ↥((_root_.Set.range f)ᶜ)) ≤ 2 :=
  hf.card_connectedComponents_compl_le_two_of_isClosed hdim
    (isCompact_range hf.isEmbedding.continuous).isClosed

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.IsSmoothEmbedding.card_connectedComponents_compl_le_two_of_compact then
    throwError "Refusing to shadow existing declaration Manifold.IsSmoothEmbedding.card_connectedComponents_compl_le_two_of_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.IsSmoothEmbedding.card_connectedComponents_compl_le_two_of_compact ``Submission.Manifold.IsSmoothEmbedding.card_connectedComponents_compl_le_two_of_compact

end Manifold
