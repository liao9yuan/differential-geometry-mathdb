import Submission.DifferentialGeometry.Topology.SphereSeparation.HeightStraightening
import Submission.DifferentialGeometry.Topology.PlanarJordan.CutPair
import Submission.DifferentialGeometry.Topology.Connected.FiniteClosedCover
import Submission.DifferentialGeometry.Topology.PlanarJordan.Innermost
import Submission.DifferentialGeometry.Topology.PlanarJordan.AmbientExtension
import Submission.DifferentialGeometry.Topology.Embedding.Factor
import Submission.DifferentialGeometry.Topology.Embedding.LinearEquiv
import Submission.DifferentialGeometry.Analysis.InnerProductSpace.EuclideanSplit

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set _root_.Manifold _root_.Submission.Manifold
open scoped _root_.ContDiff _root_.Submission.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Topology.SphereSeparation

theorem exists_planar_height_level_circle_parametrizations {e : SphereTwo → EuclideanThree}
    (he : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (a : ℝ)
    (hr : ∀ x, e x 2 = a → mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun y => e y 2) x ≠ 0) :
    Finite (ConnectedComponents {x : SphereTwo // e x 2 = a}) ∧
      ∃ (η : ConnectedComponents {x : SphereTwo // e x 2 = a} → AddCircle (1 : ℝ) → SphereTwo)
        (γ : ConnectedComponents {x : SphereTwo // e x 2 = a} →
          AddCircle (1 : ℝ) → Schoenflies.Plane),
        (∀ C, _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) (𝓡 2) ∞ (η C)) ∧
        (∀ C, _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ (γ C)) ∧
        (∀ C z, e (η C z) = (EuclideanSpace.equivProdLast 2).symm (γ C z, a)) ∧
        Pairwise (fun C D => Disjoint (_root_.Set.range (γ C)) (_root_.Set.range (γ D))) ∧
        (⋃ C, _root_.Set.range (γ C)) =
          (fun y : Schoenflies.Plane => (EuclideanSpace.equivProdLast 2).symm (y, a)) ⁻¹' _root_.Set.range e := by
  let L := EuclideanSpace.equivProdLast (𝕜 := ℝ) 2
  obtain ⟨hfinite, η, hη, hdisj, hcover⟩ := exists_source_height_level_circles he a hr
  have hheight (C) (z : AddCircle (1 : ℝ)) : e (η C z) 2 = a :=
    hcover.subset (mem_iUnion.mpr ⟨C, _root_.Set.mem_range_self z⟩)
  have hηL (C) : _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ)
      𝓘(ℝ, Schoenflies.Plane × ℝ) ∞ (fun z => L (e (η C z))) :=
    (he.comp (hη C) (by simp)).continuousLinearEquiv_comp L
  refine ⟨hfinite, η, fun C z => (L (e (η C z))).1, hη,
    fun C => (hηL C).fst_of_snd_eq_const (by simp) (fun z => hheight C z), ?_, ?_, ?_⟩
  · intro C z
    apply L.injective
    rw [L.apply_symm_apply]
    exact Prod.ext rfl (hheight C z)
  · intro C D hCD
    apply disjoint_left.mpr
    rintro x ⟨u, hu⟩ ⟨v, hv⟩
    have hEq : η C u = η D v := he.isEmbedding.injective (L.injective
      (Prod.ext (hu.trans hv.symm) ((hheight C u).trans (hheight D v).symm)))
    exact disjoint_left.mp (hdisj hCD) (_root_.Set.mem_range_self u) ⟨v, hEq.symm⟩
  · ext y
    constructor
    · intro hy
      obtain ⟨C, z, hz⟩ := mem_iUnion.mp hy
      have hL : L (e (η C z)) = (y, a) := Prod.ext hz (hheight C z)
      have heq : L.symm (y, a) = e (η C z) := by rw [← hL, L.symm_apply_apply]
      exact ⟨η C z, heq.symm⟩
    · rintro ⟨x, hx⟩
      have hxa : e x 2 = a := by rw [hx]; exact EuclideanSpace.equivProdLast_symm_last 2 _
      obtain ⟨C, z, hz⟩ := mem_iUnion.mp (hcover.symm.subset hxa)
      exact mem_iUnion.mpr ⟨C, z, by
        change (L (e (η C z))).1 = y
        rw [hz, hx, L.apply_symm_apply]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exists_planar_height_level_circle_parametrizations then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exists_planar_height_level_circle_parametrizations"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exists_planar_height_level_circle_parametrizations ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_planar_height_level_circle_parametrizations

theorem exists_planar_height_level_circles {e : SphereTwo → EuclideanThree}
    (he : _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanThree) ∞ e)
    (a : ℝ)
    (hr : ∀ x, e x 2 = a →
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, ℝ) (fun y => e y 2) x ≠ 0) :
    Finite (ConnectedComponents {x : SphereTwo // e x 2 = a}) ∧
      ∃ γ : ConnectedComponents {x : SphereTwo // e x 2 = a} →
          AddCircle (1 : ℝ) → Schoenflies.Plane,
        (∀ C, _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ (γ C)) ∧
        Pairwise (fun C D => Disjoint (_root_.Set.range (γ C)) (_root_.Set.range (γ D))) ∧
        (⋃ C, _root_.Set.range (γ C)) =
          (fun y : Schoenflies.Plane => (EuclideanSpace.equivProdLast 2).symm (y, a)) ⁻¹' _root_.Set.range e := by
  obtain ⟨hfinite, η, γ, hη, hγ, hcompat, hdisj, hcover⟩ :=
    exists_planar_height_level_circle_parametrizations he a hr
  exact ⟨hfinite, γ, hγ, hdisj, hcover⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exists_planar_height_level_circles then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exists_planar_height_level_circles"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exists_planar_height_level_circles ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_planar_height_level_circles

theorem exists_isOpen_inter_height_level_eq_of_isJordanCurve
    {e : SphereTwo → EuclideanThree} (he : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (a : ℝ) (hr : ∀ x, e x 2 = a →
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun y => e y 2) x ≠ 0)
    {C : Set Schoenflies.Plane} (hC : Schoenflies.IsJordanCurve C)
    (hsub : C ⊆ (fun y : Schoenflies.Plane =>
      (EuclideanSpace.equivProdLast 2).symm (y, a)) ⁻¹' _root_.Set.range e) :
    ∃ O : Set Schoenflies.Plane, IsOpen O ∧ O ∩
      ((fun y : Schoenflies.Plane => (EuclideanSpace.equivProdLast 2).symm (y, a)) ⁻¹'
        range e) = C := by
  obtain ⟨hfinite, γ, hγ, hdisj, hcover⟩ := exists_planar_height_level_circles he a hr
  let _ := hfinite
  have hγC (j) : Schoenflies.IsJordanCurve (_root_.Set.range (γ j)) :=
    PlanarJordan.isJordanCurve_range_of_isEmbedding_addCircle one_ne_zero (hγ j).isEmbedding
  obtain ⟨i, hCi, _⟩ := hC.isConnected.exists_unique_subset_of_iUnion_disjoint_closed
    (fun j => (hγC j).isClosed) hdisj (by rw [hcover]; exact hsub)
  have hCi' : C = _root_.Set.range (γ i) := hC.eq_of_subset (hγC i) hCi
  let V := ⋃ j : {j // j ≠ i}, _root_.Set.range (γ j.val)
  have hV : IsClosed V := isClosed_iUnion_of_finite (fun j => (hγC j.val).isClosed)
  refine ⟨Vᶜ, hV.isOpen_compl, ?_⟩
  rw [← hcover, hCi']
  ext x
  constructor
  · rintro ⟨hx, hxlevel⟩
    obtain ⟨j, hj⟩ := mem_iUnion.mp hxlevel
    by_cases hji : j = i
    · exact hji ▸ hj
    · exact False.elim (hx (mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩))
  · intro hx
    refine ⟨?_, mem_iUnion.mpr ⟨i, hx⟩⟩
    intro hxV
    obtain ⟨j, hj⟩ := mem_iUnion.mp hxV
    exact disjoint_left.mp (hdisj j.property) hj hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exists_isOpen_inter_height_level_eq_of_isJordanCurve then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exists_isOpen_inter_height_level_eq_of_isJordanCurve"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exists_isOpen_inter_height_level_eq_of_isJordanCurve ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_isOpen_inter_height_level_eq_of_isJordanCurve

theorem exists_innermost_height_level_circle {e : SphereTwo → EuclideanThree}
    (he : _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanThree) ∞ e)
    {a : ℝ} (hne : ∃ x, e x 2 = a)
    (hr : ∀ x, e x 2 = a →
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, ℝ) (fun y => e y 2) x ≠ 0) :
    ∃ γ : AddCircle (1 : ℝ) → Schoenflies.Plane,
      _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ γ ∧
      (fun y : Schoenflies.Plane => (EuclideanSpace.equivProdLast 2).symm (y, a)) ⁻¹' _root_.Set.range e ∩
        closure (Schoenflies.inside (_root_.Set.range γ)) = _root_.Set.range γ := by
  classical
  obtain ⟨hfinite, γ, hγ, hdisj, hcover⟩ := exists_planar_height_level_circles he a hr
  let I := ConnectedComponents {x : SphereTwo // e x 2 = a}
  let : Finite I := hfinite
  let : Fintype I := Fintype.ofFinite I
  have hnonempty : Nonempty I := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨ConnectedComponents.mk (⟨x, hx⟩ : {x : SphereTwo // e x 2 = a})⟩
  let : Nonempty I := hnonempty
  let curves := Finset.univ.image (fun i : I => _root_.Set.range (γ i))
  have hcurves : ∀ C ∈ curves, Schoenflies.IsJordanCurve C := by
    intro C hC
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hC
    exact PlanarJordan.isJordanCurve_range_of_isEmbedding_addCircle one_ne_zero
      (hγ i).isEmbedding
  have hpair : (curves : Set (Set Schoenflies.Plane)).Pairwise Disjoint := by
    intro C hC J hJ hCJ
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hJ
    exact hdisj (fun hij => hCJ (congrArg (fun k => _root_.Set.range (γ k)) hij))
  obtain ⟨C, hC, hinside⟩ := PlanarJordan.exists_innermost_jordan_curve curves
    (Finset.univ_nonempty.image _) hcurves hpair
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hC
  have hsep := Schoenflies.jordan_curve_theorem (hcurves _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
  refine ⟨γ i, hγ i, ?_⟩
  rw [← hcover, closure_eq_self_union_frontier, hsep.frontier_inside]
  ext y
  constructor
  · rintro ⟨hy, hyin | hy⟩
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hy
      exact False.elim (disjoint_left.mp
        (hinside _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)) hyin hj)
    · exact hy
  · intro hy
    exact ⟨mem_iUnion.mpr ⟨i, hy⟩, Or.inr hy⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exists_innermost_height_level_circle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exists_innermost_height_level_circle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exists_innermost_height_level_circle ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_innermost_height_level_circle

theorem exists_innermost_height_level_cylinder {e : SphereTwo → EuclideanThree}
    (he : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    {a : ℝ} (hne : ∃ x, e x 2 = a)
    (hr : ∀ x, e x 2 = a → mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun y => e y 2) x ≠ 0)
    {W : Set ℝ} (hW : IsOpen W) (haW : a ∈ W) :
    ∃ ε : ℝ, 0 < ε ∧ _root_.Set.Icc (a - ε) (a + ε) ⊆ W ∧
      ∃ γ : AddCircle (1 : ℝ) → Schoenflies.Plane,
        _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ γ ∧
        ∃ D : EuclideanThree ≃ₘ[ℝ] EuclideanThree,
          (∀ z, D z 2 = z 2) ∧ (∀ z, z 2 = a → D z = z) ∧
          (∀ t ∈ _root_.Set.Icc (a - ε) (a + ε),
            (fun y : Schoenflies.Plane => D ((EuclideanSpace.equivProdLast 2).symm (y, t))) ⁻¹'
              _root_.Set.range e ∩ closure (Schoenflies.inside (_root_.Set.range γ)) = _root_.Set.range γ) ∧
          ∃ K : Set EuclideanThree, IsCompact K ∧ K ⊆ {z | z 2 ∈ W} ∧ _root_.Set.EqOn D id Kᶜ := by
  obtain ⟨γ, hγ, hsection⟩ := exists_innermost_height_level_circle he hne hr
  obtain ⟨ε, hε, hεW, D, hD, hDa, hlevels, K, hK, hKW, hfix⟩ :=
    exists_height_preserving_regular_level_diffeomorph he hr hW haW
  refine ⟨ε, hε, hεW, γ, hγ, D, hD, hDa, ?_, K, hK, hKW, hfix⟩
  intro t ht
  have hpre := preimage_height_section_eq D.injective hD (hlevels t ht)
  exact (congrArg (fun S : Set Schoenflies.Plane =>
    S ∩ closure (Schoenflies.inside (_root_.Set.range γ))) hpre).trans hsection

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exists_innermost_height_level_cylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exists_innermost_height_level_cylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exists_innermost_height_level_cylinder ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_innermost_height_level_cylinder

end DifferentialGeometry.Topology.SphereSeparation
