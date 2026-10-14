import Submission.DifferentialGeometry.Topology.Manifold.CylinderCollar.CoorientedExtension
import Submission.DifferentialGeometry.Topology.Homeomorph.ProductBand
import Submission.DifferentialGeometry.Topology.Diffeomorph.FiberwiseAffine

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.Manifold

local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

private def cylinderShift (a : ℝ) :
    SphereCylinder ≃ₘ⟮SphereCylinderModel,SphereCylinderModel⟯ SphereCylinder :=
  Diffeomorph.fiberwiseAffine (fun _ => a) (fun _ => (1 : ℝ))
    contMDiff_const contMDiff_const (fun _ => one_ne_zero)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.cylinderShift
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.cylinderShift target :: scope.openDecls } }

private theorem cylinderShift_apply (a : ℝ) (q : SphereCylinder) :
    cylinderShift a q = (q.1,a + q.2) := by
  change (q.1,a + 1 * q.2) = _
  rw [one_mul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.cylinderShift_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.cylinderShift_apply target :: scope.openDecls } }

theorem exists_slab_collar_matching_of_boundary_intersection
    (P Q : PartialDiffeomorph SphereCylinderModel I SphereCylinder M ∞)
    (hP : _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ P.source)
    (hQ : _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ Q.source)
    (hzero : ∀ z : S2, Q (z,0) = P (z,1))
    (hmeet : P '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∩ Q '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ⊆
      P '' (_root_.Set.univ ×ˢ ({0} : Set ℝ)) ∪ P '' (_root_.Set.univ ×ˢ ({1} : Set ℝ))) :
    ∃ r : ℝ, 0 < r ∧
      ∃ F : SphereCylinder ≃ₘ⟮SphereCylinderModel,SphereCylinderModel⟯ SphereCylinder,
        (∀ q : SphereCylinder, |q.2| ≤ r → F q ∈ Q.source ∧ Q (F q) = P (q.1,1 + q.2)) ∧
        (∀ z : S2, F (z,0) = (z,0)) ∧
        (∀ q : SphereCylinder, (1 / 2 : ℝ) ≤ q.2 → F q = q) ∧
        F '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) = _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 := by
  let A := ((cylinderShift 1).toPartialDiffeomorph.trans P).trans Q.symm
  have hAs (z : S2) : (z,(0:ℝ)) ∈ A.source := by
    refine ⟨⟨mem_univ _,?_⟩,?_⟩
    · change cylinderShift 1 (z,0) ∈ P.source
      rw [cylinderShift_apply]
      exact hP ⟨mem_univ _,by constructor <;> norm_num⟩
    · change P (cylinderShift 1 (z,0)) ∈ Q.target
      rw [cylinderShift_apply,add_zero,← hzero]
      exact Q.map_source (hQ ⟨mem_univ _,by constructor <;> norm_num⟩)
  have hA0 (z : S2) : A (z,0) = (z,0) := by
    change Q.symm (P (cylinderShift 1 (z,0))) = _
    rw [cylinderShift_apply,add_zero,← hzero]
    exact Q.left_inv (hQ ⟨mem_univ _,by constructor <;> norm_num⟩)
  obtain ⟨σ,hσ,r,hr,F,hF,hF0,K,hK,hKU,hfix,_⟩ :=
    exists_signed_supported_collar_extension A (Diffeomorph.refl (𝓡 2) S2 ∞)
      (sphereDiffeomorphDegree_eq_one_of_preservesOrientation _
        (Diffeomorph.preservesOrientation_refl _)) hAs hA0 (-(1 / 2)) (1 / 2) (by norm_num) (by norm_num)
  have hfixed (q : SphereCylinder) (hq : (1 / 2 : ℝ) ≤ q.2) : F q = q := by
    apply hfix
    intro hqK
    exact not_lt_of_ge hq (hKU hqK).2.2
  have hFband : F '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) = _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 :=
    F.toHomeomorph.image_closed_band_of_zero_fixed hF0 (by norm_num : (1 / 2 : ℝ) ≤ 1) hfixed
  have hσone : σ = 1 := by
    rcases hσ with h | h
    · exact h
    · let z : S2 := ⟨EuclideanSpace.single 0 1,by simp⟩
      let t := _root_.Min.min r (1 / 2 : ℝ) / 2
      have ht : 0 < t := div_pos (lt_min hr (by norm_num)) (by norm_num)
      have htr : t ≤ r := by dsimp [t]; linarith [min_le_left r (1 / 2 : ℝ)]
      have ht1 : t < 1 := by dsimp [t]; linarith [min_le_right r (1 / 2 : ℝ)]
      have hFt := hF (z,t) (by rw [abs_of_pos ht]; exact htr)
      rw [h,neg_one_mul] at hFt
      have hPsrc : (z,1-t) ∈ P.source := hP ⟨mem_univ _,by constructor <;> linarith⟩
      have hPQ : Q (F (z,t)) = P (z,1-t) := by
        rw [hFt.2]
        change Q (Q.symm (P (cylinderShift 1 (z,-t)))) = _
        erw [Q.right_inv hFt.1.2]
        change P (cylinderShift 1 (z,-t)) = P (z,1-t)
        rw [cylinderShift_apply]
        rfl
      have hmem : P (z,1-t) ∈ P '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0:ℝ) 1) ∩ Q '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0:ℝ) 1) := by
        refine ⟨⟨(z,1-t),⟨mem_univ _,by constructor <;> linarith⟩,rfl⟩,F (z,t),?_,hPQ⟩
        rw [← hFband]
        exact ⟨(z,t),⟨mem_univ _,ht.le,ht1.le⟩,rfl⟩
      rcases hmeet hmem with ⟨q,hq,heq⟩ | ⟨q,hq,heq⟩
      · have hqsrc : q ∈ P.source := hP ⟨mem_univ _,by rw [hq.2]; constructor <;> norm_num⟩
        have he := congrArg Prod.snd (P.injOn hqsrc hPsrc heq)
        have hqt : q.2 = 0 := hq.2
        have hbad : (0 : ℝ) = 1-t := hqt.symm.trans he
        linarith
      · have hqsrc : q ∈ P.source := hP ⟨mem_univ _,by rw [hq.2]; constructor <;> norm_num⟩
        have he := congrArg Prod.snd (P.injOn hqsrc hPsrc heq)
        have hqt : q.2 = 1 := hq.2
        have hbad : (1 : ℝ) = 1-t := hqt.symm.trans he
        linarith
  refine ⟨r,hr,F,?_,hF0,hfixed,hFband⟩
  intro q hq
  have hh := hF q hq
  rw [hσone,one_mul] at hh
  have htarget : P (cylinderShift 1 q) ∈ Q.target := hh.1.2
  refine ⟨?_,?_⟩
  · rw [hh.2]
    exact Q.map_target htarget
  · rw [hh.2]
    change Q (Q.symm (P (cylinderShift 1 q))) = _
    erw [Q.right_inv htarget,cylinderShift_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_slab_collar_matching_of_boundary_intersection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_slab_collar_matching_of_boundary_intersection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_slab_collar_matching_of_boundary_intersection ``Submission.DifferentialGeometry.Topology.Manifold.exists_slab_collar_matching_of_boundary_intersection

theorem exists_slab_collar_matching
    (P Q : PartialDiffeomorph SphereCylinderModel I SphereCylinder M ∞)
    (hP : _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ P.source)
    (hQ : _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ Q.source)
    (hzero : ∀ z : S2, Q (z,0) = P (z,1))
    (hmeet : P '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∩ Q '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) =
      P '' (_root_.Set.univ ×ˢ ({1} : Set ℝ))) :
    ∃ r : ℝ, 0 < r ∧
      ∃ F : SphereCylinder ≃ₘ⟮SphereCylinderModel,SphereCylinderModel⟯ SphereCylinder,
        (∀ q : SphereCylinder, |q.2| ≤ r → F q ∈ Q.source ∧ Q (F q) = P (q.1,1 + q.2)) ∧
        (∀ z : S2, F (z,0) = (z,0)) ∧
        (∀ q : SphereCylinder, (1 / 2 : ℝ) ≤ q.2 → F q = q) ∧
        F '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) = _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 := by
  apply exists_slab_collar_matching_of_boundary_intersection P Q hP hQ hzero
  rw [hmeet]
  exact _root_.Set.subset_union_right

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_slab_collar_matching then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_slab_collar_matching"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_slab_collar_matching ``Submission.DifferentialGeometry.Topology.Manifold.exists_slab_collar_matching

end DifferentialGeometry.Topology.Manifold
