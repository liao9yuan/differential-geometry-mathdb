import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PrismDisk
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskExtension
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphGluing

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_isPLHomeomorphOn_bottom_union_collar_sides
    {B P D W : Set E} (hP : IsPolyhedron P) (hD : IsPolyhedron D) (hDB : D ⊆ B)
    {a b : ℝ} (hab : a < b) {ρ : E × ℝ → E}
    (hρ : IsPLHomeomorphOn ρ (P ×ˢ _root_.Set.Icc a b) W)
    (hbottom : ∀ x ∈ P, ρ (x, a) = x) (hWB : W ∩ B = P) :
    ∃ g : E × ℝ → E,
      IsPLHomeomorphOn g (D ×ˢ {a} ∪ (D ∩ P) ×ˢ _root_.Set.Icc a b)
        (D ∪ ρ '' ((D ∩ P) ×ˢ _root_.Set.Icc a b)) ∧
      EqOn g Prod.fst (D ×ˢ {a}) ∧ _root_.Set.EqOn g ρ ((D ∩ P) ×ˢ _root_.Set.Icc a b) := by
  have hI := (isPLBall_Icc hab).isPolyhedron
  have hDP := hD.inter hP
  have hside := hρ.restrict (hDP.prod hI) (_root_.Set.prod_mono _root_.Set.inter_subset_right Subset.rfl)
  have hbase := hD.isPLHomeomorphOn_fst_prod_const a
  apply exists_isPLHomeomorphOn_union
    (hD.prod (isHPolytope_singleton a).isPolyhedron) (hDP.prod hI) hbase hside
  · intro x hx
    have hxa : x = (x.1, a) := Prod.ext rfl hx.1.2
    rw [hxa]
    exact (hbottom x.1 hx.2.1.2).symm
  · rintro y ⟨hyD, hyimage⟩
    have hyW : y ∈ W := (_root_.Set.image_mono (_root_.Set.prod_mono _root_.Set.inter_subset_right Subset.rfl)).trans
      hρ.image_eq.subset hyimage
    have hyP : y ∈ P := hWB ▸ ⟨hyW, hDB hyD⟩
    exact ⟨(y, a), ⟨⟨hyD, rfl⟩, ⟨hyD, hyP⟩, le_rfl, hab.le⟩, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_bottom_union_collar_sides then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_bottom_union_collar_sides"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_bottom_union_collar_sides ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_bottom_union_collar_sides

open _root_.Classical in
theorem exists_isPLHomeomorphOn_prism_eqOn_collar_sides_of_isPLBall
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall 2 K.space)
    {B P W : Set E} (hP : IsPolyhedron P) (hKB : K.space ⊆ B)
    {a b : ℝ} (hab : a < b) {ρ : E × ℝ → E}
    (hρ : IsPLHomeomorphOn ρ (P ×ˢ _root_.Set.Icc a b) W)
    (hbottom : ∀ x ∈ P, ρ (x, a) = x) (hWB : W ∩ B = P)
    (hmeet : K.space ∩ P ⊆ (boundaryComplex 2 K).space)
    (hpatch : IsPLBall 2 (K.space ×ˢ {a} ∪ (K.space ∩ P) ×ˢ _root_.Set.Icc a b))
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces] (hL : IsPLBall 3 L.space)
    (hattach : K.space ∪ ρ '' ((K.space ∩ P) ×ˢ _root_.Set.Icc a b) ⊆ (boundaryComplex 3 L).space) :
    ∃ G : E × ℝ → E, IsPLHomeomorphOn G (K.space ×ˢ _root_.Set.Icc a b) L.space ∧
      EqOn G Prod.fst (K.space ×ˢ {a}) ∧ _root_.Set.EqOn G ρ ((K.space ∩ P) ×ˢ _root_.Set.Icc a b) := by
  let _ : DecidableEq (E × ℝ) := Classical.decEq _
  obtain ⟨g, hg, hgb, hgs⟩ := exists_isPLHomeomorphOn_bottom_union_collar_sides
    hP hK.isPolyhedron hKB hab hρ hbottom hWB
  have hprod := isPLBall_three_prod hK (isPLBall_Icc hab)
  obtain ⟨A, hAfin, hAspace⟩ := hprod.isPolyhedron.exists_simplicialComplex
  let _ : Finite A.faces := hAfin.to_subtype
  have hA : IsPLBall 3 A.space := hAspace.symm ▸ hprod
  have hpatchA : K.space ×ˢ {a} ∪ (K.space ∩ P) ×ˢ _root_.Set.Icc a b ⊆
      (boundaryComplex 3 A).space := by
    rw [boundaryComplex_space_prism K hK hab A hAspace]
    rintro x (hx | hx)
    · exact Or.inl ⟨hx.1, Or.inl hx.2⟩
    · exact Or.inr ⟨hmeet hx.1, hx.2⟩
  obtain ⟨G, hG, hGg⟩ := exists_isPLHomeomorphOn_eqOn_disk_of_boundaryComplex
    A L hA hL hpatch hpatchA hg hattach
  rw [hAspace] at hG
  exact ⟨G, hG, (hGg.mono _root_.Set.subset_union_left).trans hgb,
    (hGg.mono _root_.Set.subset_union_right).trans hgs⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_prism_eqOn_collar_sides_of_isPLBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_prism_eqOn_collar_sides_of_isPLBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_prism_eqOn_collar_sides_of_isPLBall ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_prism_eqOn_collar_sides_of_isPLBall

open _root_.Classical in
theorem exists_isPLHomeomorphOn_prism_eqOn_collar_sides_of_boundary_arcs {ι : Type*}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall 2 K.space)
    {B P W : Set E} (hP : IsPolyhedron P) (hKB : K.space ⊆ B)
    {a b : ℝ} (hab : a < b) {ρ : E × ℝ → E}
    (hρ : IsPLHomeomorphOn ρ (P ×ˢ _root_.Set.Icc a b) W)
    (hbottom : ∀ x ∈ P, ρ (x, a) = x) (hWB : W ∩ B = P)
    (d : Finset ι) (C : ι → Set E) (hC : ∀ i ∈ d, IsPLBall 1 (C i))
    (hCB : ∀ i ∈ d, C i ⊆ (boundaryComplex 2 K).space)
    (hcover : (⋃ i ∈ d, C i) = K.space ∩ P)
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces] (hL : IsPLBall 3 L.space)
    (hattach : K.space ∪ ρ '' ((K.space ∩ P) ×ˢ _root_.Set.Icc a b) ⊆ (boundaryComplex 3 L).space) :
    ∃ G : E × ℝ → E, IsPLHomeomorphOn G (K.space ×ˢ _root_.Set.Icc a b) L.space ∧
      EqOn G Prod.fst (K.space ×ˢ {a}) ∧ _root_.Set.EqOn G ρ ((K.space ∩ P) ×ˢ _root_.Set.Icc a b) := by
  have hmeet : K.space ∩ P ⊆ (boundaryComplex 2 K).space := by
    rw [← hcover]
    exact _root_.Set.iUnion₂_subset hCB
  have hpatch := isPLBall_prism_bottom_union_strips K hK hab d C hC hCB
  rw [hcover] at hpatch
  exact exists_isPLHomeomorphOn_prism_eqOn_collar_sides_of_isPLBall K hK hP hKB hab
    hρ hbottom hWB hmeet hpatch L hL hattach

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_prism_eqOn_collar_sides_of_boundary_arcs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_prism_eqOn_collar_sides_of_boundary_arcs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_prism_eqOn_collar_sides_of_boundary_arcs ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_prism_eqOn_collar_sides_of_boundary_arcs

open _root_.Classical in
theorem exists_isPLHomeomorphOn_prism_eqOn_collar_sides_of_boundary
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall 2 K.space)
    {B P W : Set E} (hP : IsPolyhedron P) (hKB : K.space ⊆ B)
    {a b : ℝ} (hab : a < b) {ρ : E × ℝ → E}
    (hρ : IsPLHomeomorphOn ρ (P ×ˢ _root_.Set.Icc a b) W)
    (hbottom : ∀ x ∈ P, ρ (x, a) = x) (hWB : W ∩ B = P)
    (hmeet : K.space ∩ P = (boundaryComplex 2 K).space)
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces] (hL : IsPLBall 3 L.space)
    (hattach : K.space ∪ ρ '' ((K.space ∩ P) ×ˢ _root_.Set.Icc a b) ⊆ (boundaryComplex 3 L).space) :
    ∃ G : E × ℝ → E, IsPLHomeomorphOn G (K.space ×ˢ _root_.Set.Icc a b) L.space ∧
      EqOn G Prod.fst (K.space ×ˢ {a}) ∧ _root_.Set.EqOn G ρ ((K.space ∩ P) ×ˢ _root_.Set.Icc a b) := by
  have hpatch : IsPLBall 2 (K.space ×ˢ {a} ∪ (K.space ∩ P) ×ˢ _root_.Set.Icc a b) := by
    rw [hmeet]
    exact isPLBall_prism_bottom_union_side K hK hab
  exact exists_isPLHomeomorphOn_prism_eqOn_collar_sides_of_isPLBall K hK hP hKB hab
    hρ hbottom hWB hmeet.subset hpatch L hL hattach

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_prism_eqOn_collar_sides_of_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_prism_eqOn_collar_sides_of_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_prism_eqOn_collar_sides_of_boundary ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_prism_eqOn_collar_sides_of_boundary

end DifferentialGeometry.Topology.PiecewiseLinear
