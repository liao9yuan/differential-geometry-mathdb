import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34OrderedAnnularBands
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34EssentialCircleOrderTransport
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCellPullback

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLCellOn.exists_lateral_annulus_eq_inter_of_disk_caps {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {S B D₀ D₁ F₀ F₁ J L : Set M} (hS : IsPLCellOn 3 S B)
    (hD : IsPLCellOn 2 D₀ J) (hF : IsPLCellOn 2 F₁ L)
    (hDU : D₀ ∪ D₁ = B) (hDI : D₀ ∩ D₁ = J)
    (hFU : F₀ ∪ F₁ = B) (hFI : F₀ ∩ F₁ = L) (hdis : Disjoint D₀ F₁) :
    ∃ (P : Set (EuclideanSpace ℝ (Fin 3))) (u : EuclideanSpace ℝ (Fin 3) → M)
      (f : (Fin 3 → ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)),
      IsPLBall 3 P ∧ IsPLHomeomorphInto 3 u P ∧ u '' P = S ∧
      IsPLHomeomorphOn f (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1)
        (f '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1)) ∧
      f '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1) ⊆ P ∧
      (u ∘ f) '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1) = D₁ ∩ F₀ ∧
      (u ∘ f) '' (stdSimplexBoundary 2 ×ˢ {0}) = J ∧
      (u ∘ f) '' (stdSimplexBoundary 2 ×ˢ {1}) = L := by
  obtain ⟨P, r, u, hr, hu, hS, hB⟩ := hS
  have hP : IsPLBall 3 P := ⟨r, hr⟩
  have hfront : frontier P ⊆ P := hP.isPolyhedron.isClosed.frontier_subset
  rw [hr.image_stdSimplexBoundary_eq_frontier] at hB
  have hBP : B ⊆ u '' P := hB ▸ _root_.Set.image_mono hfront
  have hD₀B : D₀ ⊆ B := hDU ▸ _root_.Set.subset_union_left
  have hD₁B : D₁ ⊆ B := hDU ▸ _root_.Set.subset_union_right
  have hF₀B : F₀ ⊆ B := hFU ▸ _root_.Set.subset_union_left
  have hF₁B : F₁ ⊆ B := hFU ▸ _root_.Set.subset_union_right
  let τ := Function.invFunOn u P
  have hleft : _root_.Set.LeftInvOn τ u P := hu.injOn.leftInvOn_invFunOn
  have hright : _root_.Set.RightInvOn τ u (u '' P) := hu.injOn.bijOn_image.invOn_invFunOn.2
  have hτi : _root_.Set.InjOn τ (u '' P) := by
    intro x hx y hy hxy
    rw [← hright hx, ← hright hy, hxy]
  have hτB : τ '' B = frontier P := by
    rw [hB, _root_.Set.image_image]
    exact (_root_.Set.image_congr fun x hx => hleft (hfront hx)).trans (_root_.Set.image_id' _)
  have hback (X : Set M) (hXB : X ⊆ B) : u '' (τ '' X) = X := by
    rw [_root_.Set.image_image]
    exact (_root_.Set.image_congr fun x hx => hright (hBP (hXB hx))).trans (_root_.Set.image_id' X)
  obtain ⟨q, hq, hqb⟩ := hD.exists_isPLHomeomorphOn_invFunOn hu (hD₀B.trans hBP)
  obtain ⟨v, hv, hvb⟩ := hF.exists_isPLHomeomorphOn_invFunOn hu (hF₁B.trans hBP)
  have hDU' : τ '' D₀ ∪ τ '' D₁ = frontier P := by
    rw [← _root_.Set.image_union, hDU, hτB]
  have hFU' : τ '' F₀ ∪ τ '' F₁ = frontier P := by
    rw [← _root_.Set.image_union, hFU, hτB]
  have hDI' : τ '' D₀ ∩ τ '' D₁ = τ '' J := by
    rw [← hτi.image_inter (hD₀B.trans hBP) (hD₁B.trans hBP), hDI]
  have hFI' : τ '' F₀ ∩ τ '' F₁ = τ '' L := by
    rw [← hτi.image_inter (hF₀B.trans hBP) (hF₁B.trans hBP), hFI]
  obtain ⟨f, hf, hf₀, hf₁⟩ :=
    hP.isPLSphere_frontier.exists_lateral_annulus_eq_inter_of_disk_caps
      hq hv hqb.symm hvb.symm hDU' hDI' hFU' hFI'
      (hdis.image hτi (hD₀B.trans hBP) (hF₁B.trans hBP))
  have hfP : f '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1) ⊆ P := by
    rw [hf.image_eq]
    exact (inter_subset_left.trans (hDU' ▸ _root_.Set.subset_union_right)).trans hfront
  refine ⟨P, u, f, hP, hu, hS.symm, hf.image_eq.symm ▸ hf, hfP, ?_, ?_, ?_⟩
  · rw [_root_.Set.image_comp, hf.image_eq,
      ← hτi.image_inter (hD₁B.trans hBP) (hF₀B.trans hBP),
      hback _ (inter_subset_left.trans hD₁B)]
  · rw [_root_.Set.image_comp, hf₀, hback J (hD.boundary_subset.trans hD₀B)]
  · rw [_root_.Set.image_comp, hf₁, hback L (hF.boundary_subset.trans hF₁B)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.exists_lateral_annulus_eq_inter_of_disk_caps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.exists_lateral_annulus_eq_inter_of_disk_caps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.exists_lateral_annulus_eq_inter_of_disk_caps ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.exists_lateral_annulus_eq_inter_of_disk_caps

theorem IsPLCellOn.exists_ordered_lateral_bands_of_essential_family {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {S B A A₀ A₁ : Set M} (hS : IsPLCellOn 3 S B) (hA : IsAnnulusOn A A₀ A₁)
    (hAB : A ⊆ B) (C : Set (Set M)) (hC : C.Finite)
    (hCsph : ∀ J ∈ C, IsPolyhedralSphere (n := 3) 1 J) (hCA : ∀ J ∈ C, J ⊆ A)
    (hCend : ∀ J ∈ C, Disjoint J (A₀ ∪ A₁)) (hCdisj : C.PairwiseDisjoint id)
    (hCess : ∀ J ∈ C, ¬ ∃ D : Set M, IsPLCellOn 2 D J ∧ D ⊆ A) :
    ∃ e : Fin C.ncard ≃ C, ∀ i j, i < j →
      ∃ (P : Set (EuclideanSpace ℝ (Fin 3))) (u : EuclideanSpace ℝ (Fin 3) → M)
        (f : (Fin 3 → ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)),
      IsPLBall 3 P ∧ IsPLHomeomorphInto 3 u P ∧ u '' P = S ∧
      IsPLHomeomorphOn f (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1)
        (f '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1)) ∧
      f '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1) ⊆ P ∧
      (u ∘ f) '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1) ⊆ A ∧
      (u ∘ f) '' (stdSimplexBoundary 2 ×ˢ {0}) = (e i).val ∧
      (u ∘ f) '' (stdSimplexBoundary 2 ×ˢ {1}) = (e j).val ∧
      (∀ k, (e k).val ⊆ (u ∘ f) '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1) ↔
        i ≤ k ∧ k ≤ j) ∧
      (j.val = i.val + 1 →
        Disjoint ((u ∘ f) '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Ioo (0 : ℝ) 1)) (⋃₀ C)) := by
  obtain ⟨e, D₀, D₁, hcap, -, -, hdis, hleft, hright⟩ :=
    hS.exists_ordered_disk_caps_of_essential_family hA hAB C hC hCsph hCA hCend hCdisj hCess
  refine ⟨e, ?_⟩
  intro i j hij
  obtain ⟨P, u, f, hP, hu, himageS, hf, hfP, hfimage, hf₀, hf₁⟩ :=
    hS.exists_lateral_annulus_eq_inter_of_disk_caps
      (hcap i).1 (hcap j).2.1 (hcap i).2.2.1 (hcap i).2.2.2.1
      (hcap j).2.2.1 (hcap j).2.2.2.1 (hdis i j hij)
  have hmaps : _root_.Set.MapsTo f (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1) P :=
    fun x hx => hfP ⟨x, hx, rfl⟩
  have hcont : ContinuousOn (u ∘ f) (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1) :=
    hu.continuousOn.comp hf.isPiecewiseAffineOn.continuousOn hmaps
  have hinj : _root_.Set.InjOn (u ∘ f) (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1) :=
    hu.injOn.comp hf.bijOn.injOn hmaps
  have hsubB : D₁ i ∩ D₀ j ⊆ B :=
    inter_subset_left.trans ((hcap i).2.2.1 ▸ _root_.Set.subset_union_right)
  have hsubA : D₁ i ∩ D₀ j ⊆ A := by
    have hconn := ((isConnected_stdSimplexBoundary 0).prod
      (isConnected_Icc (zero_le_one : (0 : ℝ) ≤ 1))).image (u ∘ f) hcont
    rw [hfimage] at hconn
    apply hS.subset_annulus_of_isPreconnected_of_disjoint_boundary hA hAB hsubB
      hconn.isPreconnected
    · have hne : (e i).val.Nonempty := by
        obtain ⟨T, hT⟩ := hCsph (e i).val (e i).property
        exact T.piece.bijOn.image_eq ▸ hT.nonempty.image T.piece.map
      obtain ⟨x, hx⟩ := hne
      refine ⟨x, ⟨((hcap i).2.2.2.1.superset hx).2,
        (hleft i j).mpr hij.le hx⟩, hCA (e i).val (e i).property hx⟩
    · refine disjoint_left.mpr fun x hx hxrim => ?_
      rcases hxrim with hx₀ | hx₁
      · exact disjoint_left.mp (hCend (e i).val (e i).property)
          ((hcap i).2.2.2.1.subset ⟨(hcap i).2.2.2.2.1 hx₀, hx.1⟩) (Or.inl hx₀)
      · exact disjoint_left.mp (hCend (e j).val (e j).property)
          ((hcap j).2.2.2.1.subset ⟨hx.2, (hcap j).2.2.2.2.2 hx₁⟩) (Or.inr hx₁)
  refine ⟨P, u, f, hP, hu, himageS, hf, hfP, hfimage ▸ hsubA, hf₀, hf₁, ?_, ?_⟩
  · intro k
    rw [hfimage]
    exact subset_inter_of_ordered_caps_iff hleft hright i j k
  · intro hadj
    have htrace : (⋃ k, (e k).val) = ⋃₀ C := by
      apply Subset.antisymm
      · exact _root_.Set.iUnion_subset fun k => _root_.Set.subset_sUnion_of_mem (e k).property
      · rintro x ⟨J, hJ, hxJ⟩
        obtain ⟨k, hk⟩ := e.surjective ⟨J, hJ⟩
        exact mem_iUnion.mpr ⟨k, (congrArg Subtype.val hk).symm ▸ hxJ⟩
    rw [← htrace]
    exact disjoint_open_lateral_trace_of_adjacent_caps
      (fun k => (hcap k).2.2.2.1) hdis hadj hinj hfimage hf₀ hf₁

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.exists_ordered_lateral_bands_of_essential_family then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.exists_ordered_lateral_bands_of_essential_family"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.exists_ordered_lateral_bands_of_essential_family ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.exists_ordered_lateral_bands_of_essential_family

end DifferentialGeometry.Topology.PiecewiseLinear
