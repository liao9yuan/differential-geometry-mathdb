import Submission.DifferentialGeometry.Topology.ProjectiveSpace.AffineThree
import Submission.DifferentialGeometry.Topology.ProjectiveSpace.Real
import Submission.DifferentialGeometry.Topology.ProjectiveSpace.PuncturedThree
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorphTrans

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section
open private realProjectiveThreeSplit realProjectiveThreeScalarLine
  realProjectiveThreeScalarLine_apply realProjectiveThreeScalarLine_smul
  twoSphereProdRealVector twoSphereProdRealVector_ne_zero twoSphereProdRealToThreeSphere
  twoSphereProdRealToThreeSphere_coe realProjectiveThreeNorthVector realProjectiveThreeNorthPole
  from Submission.DifferentialGeometry.Topology.ProjectiveSpace.PuncturedThree

noncomputable section

open _root_.Set
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry

def realProjectiveThreeAffineBallMap (L : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    RealProjectiveThreeSpace :=
  realProjectiveThreeAffineChart (L⁻¹ • x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.realProjectiveThreeAffineBallMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.realProjectiveThreeAffineBallMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.realProjectiveThreeAffineBallMap ``Submission.DifferentialGeometry.realProjectiveThreeAffineBallMap

@[simp] theorem realProjectiveThreeAffineBallMap_zero (L : ℝ) :
    realProjectiveThreeAffineBallMap L 0 = realProjectiveThreeSpacePuncture := by
  simp only [realProjectiveThreeAffineBallMap, smul_zero]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.realProjectiveThreeAffineBallMap_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.realProjectiveThreeAffineBallMap_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.realProjectiveThreeAffineBallMap_zero ``Submission.DifferentialGeometry.realProjectiveThreeAffineBallMap_zero

theorem realProjectiveThreeAffineBallMap_injective {L : ℝ} (hL : L ≠ 0) :
    Function.Injective (realProjectiveThreeAffineBallMap L) := by
  intro x y hxy
  have h := realProjectiveThreeAffineChart_injective hxy
  have hs := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => L • v) h
  simpa only [smul_smul, mul_inv_cancel₀ hL, one_smul] using hs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.realProjectiveThreeAffineBallMap_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.realProjectiveThreeAffineBallMap_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.realProjectiveThreeAffineBallMap_injective ``Submission.DifferentialGeometry.realProjectiveThreeAffineBallMap_injective

private theorem projectiveAffineVector_ne_zero (v : EuclideanSpace ℝ (Fin 3)) :
    realProjectiveThreeSplit.symm (v, realProjectiveThreeScalarLine 1) ≠ 0 := by
  intro h
  have hs := congrArg (fun z => (realProjectiveThreeSplit z).2 0) h
  simp only [ContinuousLinearEquiv.apply_symm_apply, map_zero,
    realProjectiveThreeScalarLine_apply] at hs
  exact one_ne_zero hs

run_cmd do
  let target := ``Submission.DifferentialGeometry.projectiveAffineVector_ne_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.projectiveAffineVector_ne_zero target :: scope.openDecls } }

theorem realProjectiveThreeAffineChart_eq_cylinder_iff
    (v : EuclideanSpace ℝ (Fin 3))
    (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) :
    realProjectiveThreeAffineChart v = realProjectiveSpaceQuotientMap
      (twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture p).1 ↔
      p.2 ≠ 0 ∧ v = p.2⁻¹ • (p.1 : EuclideanSpace ℝ (Fin 3)) := by
  have hquot := realProjectiveSpaceQuotientMap_normalize_eq_iff
    (projectiveAffineVector_ne_zero v) (twoSphereProdRealVector_ne_zero p)
  have hpoint :
      (twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture p).1 =
        (⟨NormedSpace.normalize (twoSphereProdRealVector p),
          mem_sphere_zero_iff_norm.mpr
            (NormedSpace.norm_normalize (twoSphereProdRealVector_ne_zero p))⟩ :
          Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) := by
    apply Subtype.ext
    exact twoSphereProdRealToThreeSphere_coe p
  rw [hpoint]
  change realProjectiveSpaceQuotientMap
      (⟨NormedSpace.normalize (realProjectiveThreeSplit.symm
        (v, realProjectiveThreeScalarLine 1)), _⟩ :
        Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) = _ ↔ _
  rw [hquot]
  constructor
  · rintro ⟨c, hc, heq⟩
    have hcoord := congrArg realProjectiveThreeSplit heq
    simp only [twoSphereProdRealVector, map_smul,
      ContinuousLinearEquiv.apply_symm_apply, Prod.smul_mk] at hcoord
    have hfirst : v = c • (p.1 : EuclideanSpace ℝ (Fin 3)) := congrArg Prod.fst hcoord
    have hlast : (1 : ℝ) = c * p.2 := by
      have h := congrArg
        (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 1) => z.2 0) hcoord
      change (1 : ℝ) = c * p.2 at h
      exact h
    have ht : p.2 ≠ 0 := by
      intro hzero
      rw [hzero, _root_.MulZeroClass.mul_zero] at hlast
      exact one_ne_zero hlast
    have hcInv : c = p.2⁻¹ := by
      calc
        c = (c * p.2) * p.2⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ ht, mul_one]
        _ = p.2⁻¹ := by rw [← hlast, one_mul]
    exact ⟨ht, hcInv ▸ hfirst⟩
  · rintro ⟨ht, hv⟩
    refine ⟨p.2⁻¹, inv_ne_zero ht, ?_⟩
    apply realProjectiveThreeSplit.injective
    rw [map_smul, ContinuousLinearEquiv.apply_symm_apply, twoSphereProdRealVector,
      ContinuousLinearEquiv.apply_symm_apply]
    apply Prod.ext
    · exact hv
    · ext i
      fin_cases i
      change (1 : ℝ) = p.2⁻¹ * p.2
      exact (inv_mul_cancel₀ ht).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.realProjectiveThreeAffineChart_eq_cylinder_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.realProjectiveThreeAffineChart_eq_cylinder_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.realProjectiveThreeAffineChart_eq_cylinder_iff ``Submission.DifferentialGeometry.realProjectiveThreeAffineChart_eq_cylinder_iff

theorem realProjectiveThreeCylinderMap_mem_affineBall_iff
    {L : ℝ} (hL : 0 < L)
    (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) :
    realProjectiveSpaceQuotientMap
      (twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture p).1 ∈
      realProjectiveThreeAffineBallMap L '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1 ↔
      L < |p.2| := by
  constructor
  · rintro ⟨x, hx, hxp⟩
    have h := (realProjectiveThreeAffineChart_eq_cylinder_iff (L⁻¹ • x) p).mp hxp
    have hxEq : x = (L * p.2⁻¹) • (p.1 : EuclideanSpace ℝ (Fin 3)) := by
      calc
        x = L • (L⁻¹ • x) := by rw [smul_smul, mul_inv_cancel₀ hL.ne', one_smul]
        _ = (L * p.2⁻¹) • (p.1 : EuclideanSpace ℝ (Fin 3)) := by rw [h.2, smul_smul]
    have hxnorm : ‖x‖ = L / |p.2| := by
      rw [hxEq, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos hL, abs_inv,
        norm_eq_of_mem_sphere, mul_one, div_eq_mul_inv]
    have hxlt : ‖x‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hx
    rw [hxnorm] at hxlt
    exact (div_lt_one (abs_pos.mpr h.1)).mp hxlt
  · intro ht
    have hnonzero : p.2 ≠ 0 := (abs_pos.mp (hL.trans ht))
    refine ⟨(L * p.2⁻¹) • (p.1 : EuclideanSpace ℝ (Fin 3)), ?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_mul,
        abs_of_pos hL, abs_inv, norm_eq_of_mem_sphere, mul_one, ← div_eq_mul_inv]
      exact (div_lt_one (abs_pos.mpr hnonzero)).mpr ht
    · apply (realProjectiveThreeAffineChart_eq_cylinder_iff _ p).mpr
      refine ⟨hnonzero, ?_⟩
      rw [smul_smul, ← mul_assoc, inv_mul_cancel₀ hL.ne', one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.realProjectiveThreeCylinderMap_mem_affineBall_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.realProjectiveThreeCylinderMap_mem_affineBall_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.realProjectiveThreeCylinderMap_mem_affineBall_iff ``Submission.DifferentialGeometry.realProjectiveThreeCylinderMap_mem_affineBall_iff

theorem realProjectiveThreeCylinderMap_not_mem_affineBall_iff
    {L : ℝ} (hL : 0 < L)
    (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) :
    realProjectiveSpaceQuotientMap
      (twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture p).1 ∉
      realProjectiveThreeAffineBallMap L '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1 ↔
      |p.2| ≤ L := by
  rw [realProjectiveThreeCylinderMap_mem_affineBall_iff hL, not_lt]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.realProjectiveThreeCylinderMap_not_mem_affineBall_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.realProjectiveThreeCylinderMap_not_mem_affineBall_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.realProjectiveThreeCylinderMap_not_mem_affineBall_iff ``Submission.DifferentialGeometry.realProjectiveThreeCylinderMap_not_mem_affineBall_iff

theorem realProjectiveThreeAffineBall_complement_preimage
    {L : ℝ} (hL : 0 < L) :
    (fun p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ =>
      realProjectiveSpaceQuotientMap
        (twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture p).1) ⁻¹'
      (realProjectiveThreeAffineBallMap L ''
        Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1)ᶜ =
      Set.univ ×ˢ Set.Icc (-L) L := by
  ext p
  change (_ ∉ realProjectiveThreeAffineBallMap L ''
    Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1) ↔ _
  rw [realProjectiveThreeCylinderMap_not_mem_affineBall_iff hL]
  simpa only [Set.mem_prod, Set.mem_univ, true_and, Set.mem_Icc] using
    (abs_le : |p.2| ≤ L ↔ -L ≤ p.2 ∧ p.2 ≤ L)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.realProjectiveThreeAffineBall_complement_preimage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.realProjectiveThreeAffineBall_complement_preimage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.realProjectiveThreeAffineBall_complement_preimage ``Submission.DifferentialGeometry.realProjectiveThreeAffineBall_complement_preimage

theorem realProjectiveThreeAffineBall_complement_eq_cylinder_image
    {L : ℝ} (hL : 0 < L) :
    (realProjectiveThreeAffineBallMap L ''
      Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1)ᶜ =
      (fun p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ =>
        realProjectiveSpaceQuotientMap
          (twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture p).1) ''
        (Set.univ ×ˢ Set.Icc (-L) L) := by
  ext q
  constructor
  · intro hq
    have hne : q ≠ realProjectiveThreeSpacePuncture := by
      intro heq
      apply hq
      refine ⟨0, by simp, ?_⟩
      exact (realProjectiveThreeAffineBallMap_zero L).trans heq.symm
    obtain ⟨z, hz⟩ := realProjectiveSpaceQuotientMap_surjective q
    let z' : threeSphereAwayFromRealProjectivePuncture :=
      ⟨z, fun h => hne (hz.symm.trans h)⟩
    let p := twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture.symm z'
    have hp : realProjectiveSpaceQuotientMap
        (twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture p).1 = q := by
      have h := congrArg
        (fun y : threeSphereAwayFromRealProjectivePuncture => realProjectiveSpaceQuotientMap y.1)
        (twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture.apply_symm_apply z')
      exact h.trans hz
    have hbound : |p.2| ≤ L :=
      (realProjectiveThreeCylinderMap_not_mem_affineBall_iff hL p).mp (hp ▸ hq)
    exact ⟨p, ⟨Set.mem_univ _, abs_le.mp hbound⟩, hp⟩
  · rintro ⟨p, hp, rfl⟩
    exact (realProjectiveThreeCylinderMap_not_mem_affineBall_iff hL p).mpr
      (abs_le.mpr hp.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.realProjectiveThreeAffineBall_complement_eq_cylinder_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.realProjectiveThreeAffineBall_complement_eq_cylinder_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.realProjectiveThreeAffineBall_complement_eq_cylinder_image ``Submission.DifferentialGeometry.realProjectiveThreeAffineBall_complement_eq_cylinder_image


end DifferentialGeometry

end

end

section
noncomputable section

open _root_.Set
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry

private def projectiveAffineBallScale (L : ℝ) (hL : L ≠ 0) :
    (EuclideanSpace ℝ (Fin 3)) ≃ₘ⟮𝓡 3, 𝓡 3⟯ EuclideanSpace ℝ (Fin 3) where
  toFun x := L⁻¹ • x
  invFun x := L • x
  left_inv x := by
    change L • (L⁻¹ • x) = x
    rw [smul_smul, mul_inv_cancel₀ hL, one_smul]
  right_inv x := by
    change L⁻¹ • (L • x) = x
    rw [smul_smul, inv_mul_cancel₀ hL, one_smul]
  contMDiff_toFun := (show ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin 3) => L⁻¹ • x) from
    (contDiff_id (𝕜 := ℝ)).const_smul (L⁻¹ : ℝ)).contMDiff
  contMDiff_invFun := (show ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin 3) => L • x) from
    (contDiff_id (𝕜 := ℝ)).const_smul L).contMDiff

run_cmd do
  let target := ``Submission.DifferentialGeometry.projectiveAffineBallScale
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.projectiveAffineBallScale target :: scope.openDecls } }

def realProjectiveThreeAffineBall (L : ℝ) (hL : L ≠ 0) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) (EuclideanSpace ℝ (Fin 3)) RealProjectiveThreeSpace ∞ :=
  (projectiveAffineBallScale L hL).toPartialDiffeomorph.trans
    realProjectiveThreeAffinePartialDiffeomorph

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.realProjectiveThreeAffineBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.realProjectiveThreeAffineBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.realProjectiveThreeAffineBall ``Submission.DifferentialGeometry.realProjectiveThreeAffineBall

@[simp] theorem realProjectiveThreeAffineBall_apply (L : ℝ) (hL : L ≠ 0)
    (x : EuclideanSpace ℝ (Fin 3)) :
    realProjectiveThreeAffineBall L hL x = realProjectiveThreeAffineBallMap L x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.realProjectiveThreeAffineBall_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.realProjectiveThreeAffineBall_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.realProjectiveThreeAffineBall_apply ``Submission.DifferentialGeometry.realProjectiveThreeAffineBall_apply

@[simp] theorem realProjectiveThreeAffineBall_source (L : ℝ) (hL : L ≠ 0) :
    (realProjectiveThreeAffineBall L hL).source = Set.univ := by
  change Set.univ ∩ (projectiveAffineBallScale L hL) ⁻¹'
    realProjectiveThreeAffinePartialDiffeomorph.source = Set.univ
  rw [realProjectiveThreeAffinePartialDiffeomorph_source]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.realProjectiveThreeAffineBall_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.realProjectiveThreeAffineBall_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.realProjectiveThreeAffineBall_source ``Submission.DifferentialGeometry.realProjectiveThreeAffineBall_source

theorem realProjectiveThreeAffineBall_contains_closedBall (L : ℝ) (hL : L ≠ 0) :
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2 ⊆
      (realProjectiveThreeAffineBall L hL).source := by
  rw [realProjectiveThreeAffineBall_source]
  exact Set.subset_univ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.realProjectiveThreeAffineBall_contains_closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.realProjectiveThreeAffineBall_contains_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.realProjectiveThreeAffineBall_contains_closedBall ``Submission.DifferentialGeometry.realProjectiveThreeAffineBall_contains_closedBall

theorem realProjectiveThreeAffineBall_complement_eq_slab_image
    {L : ℝ} (hL : 0 < L) :
    (realProjectiveThreeAffineBall L hL.ne' ''
      Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1)ᶜ =
      (fun p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ =>
        realProjectiveSpaceQuotientMap
          (twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture p).1) ''
        (Set.univ ×ˢ Set.Icc (-L) L) := by
  have hmaps : (realProjectiveThreeAffineBall L hL.ne' :
      EuclideanSpace ℝ (Fin 3) → RealProjectiveThreeSpace) =
      realProjectiveThreeAffineBallMap L := by
    funext x
    exact realProjectiveThreeAffineBall_apply L hL.ne' x
  rw [hmaps]
  exact realProjectiveThreeAffineBall_complement_eq_cylinder_image hL

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.realProjectiveThreeAffineBall_complement_eq_slab_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.realProjectiveThreeAffineBall_complement_eq_slab_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.realProjectiveThreeAffineBall_complement_eq_slab_image ``Submission.DifferentialGeometry.realProjectiveThreeAffineBall_complement_eq_slab_image

end DifferentialGeometry

end

end
