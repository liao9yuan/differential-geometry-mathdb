import Submission.DifferentialGeometry.Topology.Manifold.StereographicChart
import Submission.DifferentialGeometry.Topology.Manifold.StereographicClosedBall
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.BallComplement

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Metric _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology.Manifold

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S3" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

private def stereographicInversePartial (p : S3) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) E3 S3 ∞ where
  toPartialEquiv := (stereographic' 3 p).symm.toPartialEquiv
  open_source := (stereographic' 3 p).symm.open_source
  open_target := (stereographic' 3 p).symm.open_target
  contMDiffOn_toFun := (stereographicInverse_isLocalDiffeomorph p).contMDiff.contMDiffOn
  contMDiffOn_invFun := (stereographic_isLocalDiffeomorphOn p).contMDiffOn

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.stereographicInversePartial
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.stereographicInversePartial target :: scope.openDecls } }

private def doubleSpace : E3 ≃ₘ[ℝ] E3 :=
  (LinearEquiv.smulOfNeZero ℝ E3 (2 : ℝ) (by norm_num)).toContinuousLinearEquiv.toDiffeomorph

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.doubleSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.doubleSpace target :: scope.openDecls } }

private def standardHemisphereChart (p : S3) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) E3 S3 ∞ :=
  doubleSpace.toPartialDiffeomorph.trans (stereographicInversePartial p)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.standardHemisphereChart
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.standardHemisphereChart target :: scope.openDecls } }

private def oppositeHemisphereChart (p : S3) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) E3 S3 ∞ :=
  (standardHemisphereChart p).trans
    (sphereAntipodalDiffeomorph (E := EuclideanSpace ℝ (Fin 4)) (n := 3)).toPartialDiffeomorph

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.oppositeHemisphereChart
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.oppositeHemisphereChart target :: scope.openDecls } }

private theorem standardHemisphereChart_source (p : S3) :
    (standardHemisphereChart p).source = univ := by
  ext x
  change (x ∈ (_root_.Set.univ : Set E3) ∧ doubleSpace x ∈ (stereographic' 3 p).target) ↔ x ∈ _root_.Set.univ
  rw [stereographic'_target]
  simp only [_root_.Set.mem_univ, and_self]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.standardHemisphereChart_source
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.standardHemisphereChart_source target :: scope.openDecls } }

private theorem oppositeHemisphereChart_source (p : S3) :
    (oppositeHemisphereChart p).source = univ := by
  ext x
  change (x ∈ (standardHemisphereChart p).source ∧
    standardHemisphereChart p x ∈ (_root_.Set.univ : Set S3)) ↔ x ∈ _root_.Set.univ
  rw [standardHemisphereChart_source]
  simp only [_root_.Set.mem_univ, and_self]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.oppositeHemisphereChart_source
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.oppositeHemisphereChart_source target :: scope.openDecls } }

private theorem doubleSpace_image_ball : doubleSpace '' _root_.Metric.ball (0 : E3) 1 = _root_.Metric.ball 0 2 := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_ball_zero_iff]
    change ‖(2 : ℝ) • y‖ < 2
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have h := mem_ball_zero_iff.mp hy
    linarith
  · intro hx
    refine ⟨(1 / 2 : ℝ) • x, ?_, ?_⟩
    · rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      have h := mem_ball_zero_iff.mp hx
      linarith
    · change (2 : ℝ) • ((1 / 2 : ℝ) • x) = x
      rw [smul_smul]
      norm_num

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.doubleSpace_image_ball
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.doubleSpace_image_ball target :: scope.openDecls } }

private theorem doubleSpace_image_closedBall :
    doubleSpace '' _root_.Metric.closedBall (0 : E3) 1 = _root_.Metric.closedBall 0 2 := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_closedBall_zero_iff]
    change ‖(2 : ℝ) • y‖ ≤ 2
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have h := mem_closedBall_zero_iff.mp hy
    linarith
  · intro hx
    refine ⟨(1 / 2 : ℝ) • x, ?_, ?_⟩
    · rw [mem_closedBall_zero_iff, norm_smul,
        Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      have h := mem_closedBall_zero_iff.mp hx
      linarith
    · change (2 : ℝ) • ((1 / 2 : ℝ) • x) = x
      rw [smul_smul]
      norm_num

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.doubleSpace_image_closedBall
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.doubleSpace_image_closedBall target :: scope.openDecls } }

private theorem hemisphere_complement (p : S3) :
    (oppositeHemisphereChart p) '' _root_.Metric.closedBall (0 : E3) 1 =
      ((standardHemisphereChart p) '' _root_.Metric.ball (0 : E3) 1)ᶜ := by
  have h := antipodal_image_stereographic_symm_closedBall (n := 3) p (by norm_num : (0 : ℝ) < 2)
  norm_num only [show (4 : ℝ) / 2 = 2 by norm_num] at h
  change (Neg.neg ∘ ((stereographic' 3 p).symm ∘ doubleSpace)) '' _root_.Metric.closedBall 0 1 =
    (((stereographic' 3 p).symm ∘ doubleSpace) '' _root_.Metric.ball 0 1)ᶜ
  rw [_root_.Set.image_comp, _root_.Set.image_comp, _root_.Set.image_comp, doubleSpace_image_closedBall, doubleSpace_image_ball]
  exact h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.hemisphere_complement
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.hemisphere_complement target :: scope.openDecls } }

theorem exists_sphere_diffeomorph_of_complementary_ball_charts_eqOn_neighborhood
    {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [T2Space M]
    (A B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞)
    (hA : _root_.Metric.closedBall (0 : E3) 1 ⊆ A.source)
    (hB : _root_.Metric.closedBall (0 : E3) 1 ⊆ B.source)
    (hcover : B '' _root_.Metric.ball (0 : E3) 1 = (A '' _root_.Metric.closedBall (0 : E3) 1)ᶜ) :
    ∃ e : S3 ≃ₘ⟮𝓡 3, 𝓡 3⟯ M,
      ∃ a b : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 S3 ∞,
        a.source = _root_.Set.univ ∧ b.source = _root_.Set.univ ∧
        a '' _root_.Metric.closedBall (0 : E3) 1 = (b '' _root_.Metric.ball (0 : E3) 1)ᶜ ∧
        (∀ z ∈ _root_.Metric.closedBall (0 : E3) 1, e (a z) = A z) ∧
        ∃ D : E3 ≃ₘ[ℝ] E3,
          D '' _root_.Metric.closedBall (0 : E3) 1 = _root_.Metric.closedBall (0 : E3) 1 ∧
          (∀ z ∈ _root_.Metric.closedBall (0 : E3) 1, e (b z) = B (D z)) ∧
          ∃ U : Set M, IsOpen U ∧ A '' _root_.Metric.closedBall (0 : E3) 1 ⊆ U ∧
            U ⊆ (A.symm.trans a).source ∧ _root_.Set.EqOn e.symm (A.symm.trans a) U := by
  let p : S3 := ⟨EuclideanSpace.single 0 1, by simp⟩
  let b := standardHemisphereChart p
  let a := oppositeHemisphereChart p
  have ha : a.source = univ := oppositeHemisphereChart_source p
  have hb : b.source = univ := standardHemisphereChart_source p
  have hcomp : a '' _root_.Metric.closedBall (0 : E3) 1 = (b '' _root_.Metric.ball (0 : E3) 1)ᶜ :=
    hemisphere_complement p
  have hainv (z : E3) : a.symm (a z) = z := a.left_inv' (ha ▸ _root_.Set.mem_univ z)
  let P := a.symm.trans A
  have hKP : (b '' _root_.Metric.ball (0 : E3) 1)ᶜ ⊆ P.source := by
    rw [← hcomp]
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨a.map_source (ha ▸ _root_.Set.mem_univ z), ?_⟩
    change a.symm (a z) ∈ A.source
    rw [hainv z]
    exact hA hz
  have hPU : P '' (b '' _root_.Metric.ball (0 : E3) 1)ᶜ = A '' _root_.Metric.closedBall (0 : E3) 1 := by
    rw [← hcomp, _root_.Set.image_image]
    apply _root_.Set.image_congr
    intro z hz
    change A (a.symm (a z)) = A z
    rw [hainv z]
  obtain ⟨e, heP, _, D, hD, heB, O, hO, hKO, hOP, heO⟩ :=
    exists_diffeomorph_of_ball_complement_and_ball b P B
      (hb ▸ _root_.Set.subset_univ _) hKP hB hPU hcover
  have heA (z : E3) (hz : z ∈ _root_.Metric.closedBall (0 : E3) 1) : e (a z) = A z := by
    have he := heP (hcomp ▸ _root_.Set.mem_image_of_mem a hz)
    change e (a z) = A (a.symm (a z)) at he
    rwa [hainv z] at he
  refine ⟨e,a,b,ha,hb,hcomp,heA,D,hD,heB,e '' O,e.toHomeomorph.isOpenMap _ hO,?_,?_,?_⟩
  · rintro _ ⟨z,hz,rfl⟩
    exact ⟨a z,hKO (hcomp ▸ _root_.Set.mem_image_of_mem a hz),heA z hz⟩
  · rintro _ ⟨x,hx,rfl⟩
    have hxP := hOP hx
    have he : e x = A (a.symm x) := heO hx
    refine ⟨?_,ha ▸ _root_.Set.mem_univ _⟩
    rw [he]
    exact A.map_source hxP.2
  · rintro _ ⟨x,hx,rfl⟩
    rw [e.symm_apply_apply]
    change x = a (A.symm (e x))
    have he : e x = A (a.symm x) := heO hx
    have hAs : a.symm x ∈ A.source := (hOP hx).2
    have hAi : A.symm (A (a.symm x)) = a.symm x := A.left_inv hAs
    rw [he,hAi]
    exact (a.right_inv (hOP hx).1).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_sphere_diffeomorph_of_complementary_ball_charts_eqOn_neighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_sphere_diffeomorph_of_complementary_ball_charts_eqOn_neighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_sphere_diffeomorph_of_complementary_ball_charts_eqOn_neighborhood ``Submission.DifferentialGeometry.Topology.Manifold.exists_sphere_diffeomorph_of_complementary_ball_charts_eqOn_neighborhood


theorem exists_sphere_diffeomorph_of_complementary_ball_charts
    {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [T2Space M]
    (A B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞)
    (hA : _root_.Metric.closedBall (0 : E3) 1 ⊆ A.source)
    (hB : _root_.Metric.closedBall (0 : E3) 1 ⊆ B.source)
    (hcover : B '' _root_.Metric.ball (0 : E3) 1 = (A '' _root_.Metric.closedBall (0 : E3) 1)ᶜ) :
    ∃ e : S3 ≃ₘ⟮𝓡 3, 𝓡 3⟯ M,
      ∃ a b : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 S3 ∞,
        a.source = _root_.Set.univ ∧ b.source = _root_.Set.univ ∧
        a '' _root_.Metric.closedBall (0 : E3) 1 = (b '' _root_.Metric.ball (0 : E3) 1)ᶜ ∧
        (∀ z ∈ _root_.Metric.closedBall (0 : E3) 1, e (a z) = A z) ∧
        ∃ D : E3 ≃ₘ[ℝ] E3,
          D '' _root_.Metric.closedBall (0 : E3) 1 = _root_.Metric.closedBall (0 : E3) 1 ∧
          ∀ z ∈ _root_.Metric.closedBall (0 : E3) 1, e (b z) = B (D z) := by
  obtain ⟨e,a,b,ha,hb,hab,heA,D,hD,heB,_⟩ :=
    exists_sphere_diffeomorph_of_complementary_ball_charts_eqOn_neighborhood A B hA hB hcover
  exact ⟨e,a,b,ha,hb,hab,heA,D,hD,heB⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_sphere_diffeomorph_of_complementary_ball_charts then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_sphere_diffeomorph_of_complementary_ball_charts"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_sphere_diffeomorph_of_complementary_ball_charts ``Submission.DifferentialGeometry.Topology.Manifold.exists_sphere_diffeomorph_of_complementary_ball_charts

end DifferentialGeometry.Topology.Manifold
