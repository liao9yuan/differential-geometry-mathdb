import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PolygonalSchoenflies
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphGluing
import Submission.DifferentialGeometry.External.Schoenflies.BoundaryContinuity2

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_isPLHomeomorphOn_eqOn_crosscut
    {J P J' P' : Set (EuclideanSpace ℝ (Fin 2))} (hJ : IsPLSphere 1 J) (hP : IsPLBall 1 P)
    {p q : EuclideanSpace ℝ (Fin 2)} (hcross : Schoenflies.IsCrosscut J P p q)
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hf : IsPLHomeomorphOn f (J ∪ P) (J' ∪ P')) (hfJ : f '' J = J') (hfP : f '' P = P')
    (hcross' : Schoenflies.IsCrosscut J' P' (f p) (f q)) :
    ∃ G : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
      IsPLHomeomorphOn G (closure (Schoenflies.inside J)) (closure (Schoenflies.inside J')) ∧
        EqOn G f (J ∪ P) := by
  have hfJ' : IsPLHomeomorphOn f J J' :=
    hfJ ▸ hf.restrict hJ.isPolyhedron _root_.Set.subset_union_left
  have hfP' : IsPLHomeomorphOn f P P' :=
    hfP ▸ hf.restrict hP.isPolyhedron _root_.Set.subset_union_right
  have hJ' := hJ.of_isPLHomeomorphOn hfJ'
  have hP' := hP.of_isPLHomeomorphOn hfP'
  have hpq : p ≠ q := by
    obtain ⟨γ, -, hi, -, hγ0, hγ1⟩ := hcross.arc
    intro hpq
    exact zero_ne_one (hi Schoenflies.zero_mem_I Schoenflies.one_mem_I
      (hγ0.trans (hpq.trans hγ1.symm)))
  obtain ⟨A, B, hcut, -, -⟩ := exists_isCutPair_isPLBall_of_isPLSphere_one hJ
    hcross.left_mem hcross.right_mem hpq
  have hcut' : Schoenflies.IsCutPair J' (f p) (f q) (f '' A) (f '' B) := by
    rw [← hfJ]
    exact hcut.image hfJ'.isPiecewiseAffineOn.continuousOn hfJ'.bijOn.injOn
  have hAP := isPLSphere_one_union_of_isCrosscut hJ hP hcross hcut
  have hBP := isPLSphere_one_union_of_isCrosscut hJ hP hcross hcut.symm
  have hAP' := isPLSphere_one_union_of_isCrosscut hJ' hP' hcross' hcut'
  have hBP' := isPLSphere_one_union_of_isCrosscut hJ' hP' hcross' hcut'.symm
  let D₁ := closure (Schoenflies.inside (A ∪ P))
  let D₂ := closure (Schoenflies.inside (B ∪ P))
  let D₁' := closure (Schoenflies.inside (f '' A ∪ P'))
  let D₂' := closure (Schoenflies.inside (f '' B ∪ P'))
  have hD₁ : IsPLBall 2 D₁ := isPLBall_closure_inside_of_isPLSphere_one hAP
  have hD₂ : IsPLBall 2 D₂ := isPLBall_closure_inside_of_isPLSphere_one hBP
  have hD₁' : IsPLBall 2 D₁' := isPLBall_closure_inside_of_isPLSphere_one hAP'
  have hD₂' : IsPLBall 2 D₂' := isPLBall_closure_inside_of_isPLSphere_one hBP'
  have hfr₁ : frontier D₁ = A ∪ P := frontier_closure_inside_of_isPLSphere_one hAP
  have hfr₂ : frontier D₂ = B ∪ P := frontier_closure_inside_of_isPLSphere_one hBP
  have hfr₁' : frontier D₁' = f '' A ∪ P' := frontier_closure_inside_of_isPLSphere_one hAP'
  have hfr₂' : frontier D₂' = f '' B ∪ P' := frontier_closure_inside_of_isPLSphere_one hBP'
  have hf₁ : IsPLHomeomorphOn f (frontier D₁) (frontier D₁') := by
    rw [hfr₁, hfr₁']
    have h := hf.restrict hAP.isPolyhedron (_root_.Set.union_subset_union_left P hcut.fst_subset)
    rwa [_root_.Set.image_union, hfP] at h
  have hf₂ : IsPLHomeomorphOn f (frontier D₂) (frontier D₂') := by
    rw [hfr₂, hfr₂']
    have h := hf.restrict hBP.isPolyhedron (_root_.Set.union_subset_union_left P hcut.snd_subset)
    rwa [_root_.Set.image_union, hfP] at h
  obtain ⟨G₁, hG₁, heq₁⟩ := exists_isPLHomeomorphOn_of_frontier hD₁ hD₁' hf₁
  obtain ⟨G₂, hG₂, heq₂⟩ := exists_isPLHomeomorphOn_of_frontier hD₂ hD₂' hf₂
  rw [hfr₁] at heq₁
  rw [hfr₂] at heq₂
  have hinter : D₁ ∩ D₂ = P := PlanarJordan.closure_inside_inter_of_isCrosscut hcross hcut
  have hinter' : D₁' ∩ D₂' = P' := PlanarJordan.closure_inside_inter_of_isCrosscut hcross' hcut'
  have hagree : _root_.Set.EqOn G₁ G₂ (D₁ ∩ D₂) := by
    rw [hinter]
    exact fun x hx => (heq₁ (Or.inr hx)).trans (heq₂ (Or.inr hx)).symm
  have hsurj : _root_.Set.SurjOn G₁ (D₁ ∩ D₂) (D₁' ∩ D₂') := by
    rw [hinter, hinter']
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hfP'.bijOn.surjOn hy
    exact ⟨x, hx, (heq₁ (Or.inr hx)).trans hxy⟩
  obtain ⟨G, hG, hGleft, hGright⟩ := exists_isPLHomeomorphOn_union
    hD₁.isPolyhedron hD₂.isPolyhedron hG₁ hG₂ hagree hsurj
  have hsub₁ : A ∪ P ⊆ D₁ := hfr₁.symm.subset.trans
    (frontier_subset_closure.trans hD₁.isPolyhedron.isClosed.closure_eq.subset)
  have hsub₂ : B ∪ P ⊆ D₂ := hfr₂.symm.subset.trans
    (frontier_subset_closure.trans hD₂.isPolyhedron.isClosed.closure_eq.subset)
  have hleft : _root_.Set.EqOn G f (A ∪ P) :=
    fun x hx => (hGleft (hsub₁ hx)).trans (heq₁ hx)
  have hright : _root_.Set.EqOn G f (B ∪ P) :=
    fun x hx => (hGright (hsub₂ hx)).trans (heq₂ hx)
  refine ⟨G, ?_, ?_⟩
  · have hun : D₁ ∪ D₂ = closure (Schoenflies.inside J) :=
      PlanarJordan.closure_inside_union_of_isCrosscut hcross hcut
    have hun' : D₁' ∪ D₂' = closure (Schoenflies.inside J') :=
      PlanarJordan.closure_inside_union_of_isCrosscut hcross' hcut'
    rwa [hun, hun'] at hG
  · rintro x (hx | hx)
    · rw [← hcut.union_eq] at hx
      exact hx.elim (fun h => hleft (Or.inl h)) (fun h => hright (Or.inl h))
    · exact hleft (Or.inr hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_eqOn_crosscut then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_eqOn_crosscut"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_eqOn_crosscut ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_eqOn_crosscut

theorem exists_isPLHomeomorphOn_eqOn_curve_and_crosscut
    {J P J' P' : Set (EuclideanSpace ℝ (Fin 2))} (hJ : IsPLSphere 1 J) (hP : IsPLBall 1 P)
    {p q : EuclideanSpace ℝ (Fin 2)} (hcross : Schoenflies.IsCrosscut J P p q)
    {f g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hf : IsPLHomeomorphOn f J J') (hg : IsPLHomeomorphOn g P P')
    (hgp : g p = f p) (hgq : g q = f q)
    (hcross' : Schoenflies.IsCrosscut J' P' (f p) (f q)) :
    ∃ G : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
      IsPLHomeomorphOn G (closure (Schoenflies.inside J)) (closure (Schoenflies.inside J')) ∧
        EqOn G f J ∧ _root_.Set.EqOn G g P := by
  have hinter : J ∩ P = {p, q} := by rw [_root_.Set.inter_comm, hcross.inter_eq]
  have hinter' : J' ∩ P' = {f p, f q} := by rw [_root_.Set.inter_comm, hcross'.inter_eq]
  have heq : _root_.Set.EqOn f g (J ∩ P) := by
    rw [hinter]
    rintro x (rfl | rfl)
    · exact hgp.symm
    · exact hgq.symm
  have hsurj : _root_.Set.SurjOn f (J ∩ P) (J' ∩ P') := by
    rw [hinter, hinter']
    rintro y (rfl | rfl)
    · exact ⟨p, by simp, rfl⟩
    · exact ⟨q, by simp, rfl⟩
  obtain ⟨h, hh, hhf, hhg⟩ := exists_isPLHomeomorphOn_union
    hJ.isPolyhedron hP.isPolyhedron hf hg heq hsurj
  have hp : h p = f p := hhf hcross.left_mem
  have hq : h q = f q := hhf hcross.right_mem
  obtain ⟨G, hG, hGh⟩ := exists_isPLHomeomorphOn_eqOn_crosscut hJ hP hcross hh
    (hhf.image_eq.trans hf.image_eq) (hhg.image_eq.trans hg.image_eq) (by rwa [hp, hq])
  exact ⟨G, hG, fun x hx => (hGh (Or.inl hx)).trans (hhf hx),
    fun x hx => (hGh (Or.inr hx)).trans (hhg hx)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_eqOn_curve_and_crosscut then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_eqOn_curve_and_crosscut"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_eqOn_curve_and_crosscut ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_eqOn_curve_and_crosscut

theorem exists_isPLHomeomorphOn_map_crosscut_eqOn_curve
    {J P J' P' : Set (EuclideanSpace ℝ (Fin 2))} (hJ : IsPLSphere 1 J)
    (hP : IsPLBall 1 P) (hP' : IsPLBall 1 P')
    {p q : EuclideanSpace ℝ (Fin 2)} (hcross : Schoenflies.IsCrosscut J P p q)
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)} (hf : IsPLHomeomorphOn f J J')
    (hcross' : Schoenflies.IsCrosscut J' P' (f p) (f q)) :
    ∃ G : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
      IsPLHomeomorphOn G (closure (Schoenflies.inside J)) (closure (Schoenflies.inside J')) ∧
        EqOn G f J ∧ G '' P = P' := by
  obtain ⟨g, hg, hgp, hgq⟩ := exists_isPLHomeomorphOn_of_isArcBetween hP hP' hcross.arc hcross'.arc
  obtain ⟨G, hG, hGf, hGg⟩ := exists_isPLHomeomorphOn_eqOn_curve_and_crosscut
    hJ hP hcross hf hg hgp hgq hcross'
  exact ⟨G, hG, hGf, hGg.image_eq.trans hg.image_eq⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_map_crosscut_eqOn_curve then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_map_crosscut_eqOn_curve"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_map_crosscut_eqOn_curve ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_map_crosscut_eqOn_curve

end DifferentialGeometry.Topology.PiecewiseLinear
