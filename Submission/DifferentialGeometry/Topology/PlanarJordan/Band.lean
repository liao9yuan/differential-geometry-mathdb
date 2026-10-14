import Submission.DifferentialGeometry.Topology.Connected.FiniteClosedCover
import Submission.DifferentialGeometry.Topology.PlanarJordan.Innermost

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PlanarJordan

theorem exists_band_edge_components {ι : Type*} [Finite ι]
    (C : ι → Set Schoenflies.Plane) (hC : ∀ i, Schoenflies.IsJordanCurve (C i))
    (hdisj : Pairwise (fun i j => Disjoint (C i) (C j)))
    {B : ℝ × ℝ → Schoenflies.Plane} {h : ℝ}
    (hB : ContinuousOn B (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ _root_.Set.Icc (-h) h)) (hh : 0 ≤ h)
    (hlevel : ∀ z ∈ _root_.Set.Icc (-1 : ℝ) 1 ×ˢ _root_.Set.Icc (-h) h,
      B z ∈ ⋃ i, C i ↔ z.1 = -1 ∨ z.1 = 1) :
    (∀ a ∈ ({-1, 1} : Set ℝ), ∃! i,
      (fun u => B (a, u)) '' _root_.Set.Icc (-h) h ⊆ C i) ∧
      ∀ i, B '' (_root_.Set.Ioo (-1 : ℝ) 1 ×ˢ _root_.Set.Icc (-h) h) ⊆ Schoenflies.inside (C i) ∨
        B '' (_root_.Set.Ioo (-1 : ℝ) 1 ×ˢ _root_.Set.Icc (-h) h) ⊆ Schoenflies.outside (C i) := by
  have hI : IsConnected (_root_.Set.Icc (-h) h) := isConnected_Icc (by linarith)
  constructor
  · intro a ha
    have haedge : a = -1 ∨ a = 1 := by simpa only [_root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff] using ha
    have haI : a ∈ _root_.Set.Icc (-1 : ℝ) 1 := by rcases haedge with ha | ha <;> rw [ha] <;> norm_num
    have hcont : ContinuousOn (fun u => B (a, u)) (_root_.Set.Icc (-h) h) :=
      hB.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hu => ⟨haI, hu⟩)
    apply (hI.image _ hcont).exists_unique_subset_of_iUnion_disjoint_closed
      (fun i => (hC i).isCompact.isClosed) hdisj
    rintro _ ⟨u, hu, rfl⟩
    exact (hlevel (a, u) ⟨haI, hu⟩).mpr haedge
  · intro i
    have hrect : IsConnected (_root_.Set.Ioo (-1 : ℝ) 1 ×ˢ _root_.Set.Icc (-h) h) :=
      (isConnected_Ioo (by norm_num : (-1 : ℝ) < 1)).prod hI
    have himage := hrect.image B (hB.mono (_root_.Set.prod_mono _root_.Set.Ioo_subset_Icc_self Subset.rfl))
    have havoid : Disjoint (B '' (_root_.Set.Ioo (-1 : ℝ) 1 ×ˢ _root_.Set.Icc (-h) h)) (C i) := by
      apply disjoint_left.mpr
      rintro y ⟨z, hz, rfl⟩ hy
      have heq := (hlevel z ⟨⟨hz.1.1.le, hz.1.2.le⟩, hz.2⟩).mp (mem_iUnion.mpr ⟨i, hy⟩)
      rcases heq with heq | heq <;> linarith [hz.1.1, hz.1.2]
    obtain ⟨W, V, hWV, hsub⟩ := (Schoenflies.jordan_curve_theorem (hC i)).exists_isRegionPair_subset
      himage.isPreconnected himage.nonempty havoid
    rcases hWV with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl hsub
    · exact Or.inr hsub

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PlanarJordan.exists_band_edge_components then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PlanarJordan.exists_band_edge_components"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PlanarJordan.exists_band_edge_components ``Submission.DifferentialGeometry.Topology.PlanarJordan.exists_band_edge_components

private theorem band_subset_region_of_edge
    {C V : Set Schoenflies.Plane} (hC : Schoenflies.IsSeparating C)
    (hV : Schoenflies.IsRegionOf C V) {B : ℝ × ℝ → Schoenflies.Plane}
    {h : ℝ} (hB : ContinuousOn B (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ _root_.Set.Icc (-h) h)) (hh : 0 ≤ h)
    (havoid : ∀ z ∈ _root_.Set.Ioo (-1 : ℝ) 1 ×ˢ _root_.Set.Icc (-h) h, B z ∉ C)
    {a : ℝ} (ha : a ∈ _root_.Set.Icc (-1 : ℝ) 1) (hedge : B (a, 0) ∈ V) :
    B '' (_root_.Set.Ioo (-1 : ℝ) 1 ×ˢ _root_.Set.Icc (-h) h) ⊆ V := by
  let S := B '' (_root_.Set.Ioo (-1 : ℝ) 1 ×ˢ _root_.Set.Icc (-h) h)
  have hS : IsConnected S := ((isConnected_Ioo (by norm_num : (-1 : ℝ) < 1)).prod
    (isConnected_Icc (by linarith : -h ≤ h))).image B
      (hB.mono (_root_.Set.prod_mono _root_.Set.Ioo_subset_Icc_self Subset.rfl))
  have hp : B (a, 0) ∈ closure S := by
    apply ((hB (a, 0) ⟨ha, by constructor <;> linarith⟩).mono
      (_root_.Set.prod_mono _root_.Set.Ioo_subset_Icc_self Subset.rfl)).mem_closure_image
    rw [closure_prod_eq, closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1), isClosed_Icc.closure_eq]
    exact ⟨ha, by constructor <;> linarith⟩
  have hmeet : (S ∩ V).Nonempty := by
    obtain ⟨x, hxV, hxS⟩ := mem_closure_iff.mp hp V (hV.isOpen hC) hedge
    exact ⟨x, hxS, hxV⟩
  obtain ⟨W, hVW⟩ : ∃ W, Schoenflies.IsRegionPair C V W := by
    rcases hV with rfl | rfl
    · exact ⟨Schoenflies.outside C, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨Schoenflies.inside C, Or.inr ⟨rfl, rfl⟩⟩
  apply hS.isPreconnected.subset_left_of_subset_union (hVW.left.isOpen hC)
    (hVW.right.isOpen hC) hVW.disjoint ?_ hmeet
  rw [hVW.union_eq]
  rintro _ ⟨z, hz, rfl⟩
  exact havoid z hz

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PlanarJordan.band_subset_region_of_edge
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PlanarJordan.band_subset_region_of_edge target :: scope.openDecls } }

theorem band_regions_of_disjoint_attaching_curves
    {C J : Set Schoenflies.Plane} (hC : Schoenflies.IsJordanCurve C)
    (hJ : Schoenflies.IsJordanCurve J) (hdisj : Disjoint C J)
    {B : ℝ × ℝ → Schoenflies.Plane} {h : ℝ}
    (hB : ContinuousOn B (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ _root_.Set.Icc (-h) h)) (hh : 0 ≤ h)
    (havoid : ∀ z ∈ _root_.Set.Ioo (-1 : ℝ) 1 ×ˢ _root_.Set.Icc (-h) h, B z ∉ C ∧ B z ∉ J)
    (hleft : B (-1, 0) ∈ C) (hright : B (1, 0) ∈ J) :
    let S := B '' (_root_.Set.Ioo (-1 : ℝ) 1 ×ˢ _root_.Set.Icc (-h) h)
    (C ⊆ Schoenflies.inside J ∧ J ⊆ Schoenflies.outside C ∧
      S ⊆ Schoenflies.outside C ∩ Schoenflies.inside J) ∨
      (J ⊆ Schoenflies.inside C ∧ C ⊆ Schoenflies.outside J ∧
        S ⊆ Schoenflies.inside C ∩ Schoenflies.outside J) ∨
      (C ⊆ Schoenflies.outside J ∧ J ⊆ Schoenflies.outside C ∧
        S ⊆ Schoenflies.outside C ∩ Schoenflies.outside J) := by
  have hCs := Schoenflies.jordan_curve_theorem hC
  have hJs := Schoenflies.jordan_curve_theorem hJ
  rcases disjoint_jordan_curves_trichotomy hC hJ hdisj with ⟨hCJ, hJC⟩ | ⟨hJC, hCJ⟩ | ⟨hCJ, hJC⟩
  · exact Or.inl ⟨hCJ, hJC, _root_.Set.subset_inter
      (band_subset_region_of_edge hCs (Or.inr rfl) hB hh (fun z hz => (havoid z hz).1)
        (by norm_num) (hJC hright))
      (band_subset_region_of_edge hJs (Or.inl rfl) hB hh (fun z hz => (havoid z hz).2)
        (by norm_num) (hCJ hleft))⟩
  · exact Or.inr (Or.inl ⟨hJC, hCJ, _root_.Set.subset_inter
      (band_subset_region_of_edge hCs (Or.inl rfl) hB hh (fun z hz => (havoid z hz).1)
        (by norm_num) (hJC hright))
      (band_subset_region_of_edge hJs (Or.inr rfl) hB hh (fun z hz => (havoid z hz).2)
        (by norm_num) (hCJ hleft))⟩)
  · exact Or.inr (Or.inr ⟨hCJ, hJC, _root_.Set.subset_inter
      (band_subset_region_of_edge hCs (Or.inr rfl) hB hh (fun z hz => (havoid z hz).1)
        (by norm_num) (hJC hright))
      (band_subset_region_of_edge hJs (Or.inr rfl) hB hh (fun z hz => (havoid z hz).2)
        (by norm_num) (hCJ hleft))⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PlanarJordan.band_regions_of_disjoint_attaching_curves then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PlanarJordan.band_regions_of_disjoint_attaching_curves"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PlanarJordan.band_regions_of_disjoint_attaching_curves ``Submission.DifferentialGeometry.Topology.PlanarJordan.band_regions_of_disjoint_attaching_curves

end DifferentialGeometry.Topology.PlanarJordan
