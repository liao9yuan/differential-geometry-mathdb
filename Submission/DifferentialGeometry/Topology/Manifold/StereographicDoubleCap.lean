import Submission.DifferentialGeometry.Topology.Manifold.StereographicClosedBall
import Submission.DifferentialGeometry.Topology.Manifold.StereographicCylinder
import Submission.DifferentialGeometry.Geometry.Metric.PolarCoordinates
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SphereUnitFilling
import Mathlib.Geometry.Manifold.Instances.Icc

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.Topology.Manifold

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.E3 target :: scope.openDecls } }
private abbrev E4 := EuclideanSpace ℝ (Fin 4)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.E4
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.E4 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.S2 target :: scope.openDecls } }
private abbrev S3 := Metric.sphere (0 : E4) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.S3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.S3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE4HAddOfNat : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE4HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE4HAddOfNat target :: scope.openDecls } }

theorem stereographic_double_cap_complement (P : S3) {a b : ℝ} (hb : 0 < b) :
    (((stereographic' 3 P).symm '' Metric.ball 0 a) ∪
      Neg.neg '' ((stereographic' 3 P).symm '' Metric.ball 0 (4 / b)))ᶜ =
        (stereographic' 3 P).symm '' (Metric.closedBall 0 b \ Metric.ball 0 a) := by
  let e := (stereographic' 3 P).symm
  have hinj : _root_.Function.Injective e := e.isOpenEmbedding (by simp [e]) |>.injective
  have houter := antipodal_image_stereographic_symm_closedBall (n := 3) P (by positivity : 0 < 4 / b)
  have hcancel : 4 / (4 / b) = b := by field_simp
  rw [hcancel] at houter
  have hout (x : S3) : x ∉ Neg.neg '' (e '' Metric.ball 0 (4 / b)) ↔
      x ∈ e '' Metric.closedBall 0 b := by
    have hneg : x ∈ Neg.neg '' (e '' Metric.ball 0 (4 / b)) ↔
        -x ∈ e '' Metric.ball 0 (4 / b) := by
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa only [neg_neg] using hy
      · intro hx
        exact ⟨-x, hx, neg_neg x⟩
    rw [hneg]
    change -x ∈ (e '' Metric.ball 0 (4 / b))ᶜ ↔ _
    rw [← houter]
    constructor
    · rintro ⟨y, hy, heq⟩
      have hxy : y = x := neg_injective heq
      exact hxy ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  ext x
  change x ∉ e '' Metric.ball 0 a ∪ Neg.neg '' (e '' Metric.ball 0 (4 / b)) ↔ _
  rw [_root_.Set.mem_union, not_or, hout]
  constructor
  · rintro ⟨hx, y, hy, rfl⟩
    exact ⟨y, ⟨hy, fun hya => hx ⟨y, hya, rfl⟩⟩, rfl⟩
  · rintro ⟨y, ⟨hy, hya⟩, rfl⟩
    refine ⟨?_, ⟨y, hy, rfl⟩⟩
    rintro ⟨z, hz, heq⟩
    exact hya (hinj heq ▸ hz)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.stereographic_double_cap_complement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.stereographic_double_cap_complement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.stereographic_double_cap_complement ``Submission.DifferentialGeometry.Topology.Manifold.stereographic_double_cap_complement

def closedStereographicCylinderMap (P : S3) (a b : ℝ)
    (p : S2 × _root_.Set.Icc (0 : ℝ) 1) : S3 :=
  (stereographic' 3 P).symm ((a + (b - a) * p.2.val) • p.1.val)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.closedStereographicCylinderMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.closedStereographicCylinderMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.closedStereographicCylinderMap ``Submission.DifferentialGeometry.Topology.Manifold.closedStereographicCylinderMap

theorem continuous_closedStereographicCylinderMap (P : S3) (a b : ℝ) :
    Continuous (closedStereographicCylinderMap P a b) :=
  ((stereographic' 3 P).symm.isOpenEmbedding (by simp)).continuous.comp
    ((continuous_const.add (continuous_const.mul (continuous_subtype_val.comp continuous_snd))).smul
      (continuous_subtype_val.comp continuous_fst))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.continuous_closedStereographicCylinderMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.continuous_closedStereographicCylinderMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.continuous_closedStereographicCylinderMap ``Submission.DifferentialGeometry.Topology.Manifold.continuous_closedStereographicCylinderMap

theorem closedStereographicCylinderMap_injective (P : S3) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) : _root_.Function.Injective (closedStereographicCylinderMap P a b) := by
  intro p q h
  have heq := ((stereographic' 3 P).symm.isOpenEmbedding (by simp)).injective h
  have hp : 0 < a + (b - a) * p.2.val := by nlinarith [p.2.property.1]
  have hq : 0 < a + (b - a) * q.2.val := by nlinarith [q.2.property.1]
  have hn := congrArg _root_.Norm.norm heq
  simp only [norm_smul, Real.norm_of_nonneg hp.le, Real.norm_of_nonneg hq.le,
    norm_eq_of_mem_sphere, mul_one] at hn
  have ht : p.2.val = q.2.val := by nlinarith
  apply Prod.ext _ (Subtype.ext ht)
  apply Subtype.ext
  change (a + (b - a) * p.2.val) • p.1.val = (a + (b - a) * q.2.val) • q.1.val at heq
  rw [ht] at heq
  exact smul_right_injective E3 hq.ne' heq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.closedStereographicCylinderMap_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.closedStereographicCylinderMap_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.closedStereographicCylinderMap_injective ``Submission.DifferentialGeometry.Topology.Manifold.closedStereographicCylinderMap_injective

theorem range_closedStereographicCylinderMap (P : S3) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) :
    _root_.Set.range (closedStereographicCylinderMap P a b) =
      (stereographic' 3 P).symm '' (Metric.closedBall 0 b \ Metric.ball 0 a) := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    have hr : 0 < a + (b - a) * p.2.val := by nlinarith [p.2.property.1]
    refine ⟨(a + (b - a) * p.2.val) • p.1.val, ⟨?_, ?_⟩, rfl⟩
    · rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg hr.le,
        norm_eq_of_mem_sphere, mul_one]
      nlinarith [p.2.property.2]
    · rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg hr.le,
        norm_eq_of_mem_sphere, mul_one]
      nlinarith [p.2.property.1]
  · rintro ⟨y, ⟨hyb, hya⟩, rfl⟩
    have hya' : a ≤ ‖y‖ := by simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hya
    have hyb' : ‖y‖ ≤ b := by simpa only [Metric.mem_closedBall, dist_zero_right] using hyb
    have hypos : 0 < ‖y‖ := ha.trans_le hya'
    let z : S2 := ⟨‖y‖⁻¹ • y, by
      rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_of_nonneg (by positivity),
        inv_mul_cancel₀ hypos.ne']⟩
    let t : _root_.Set.Icc (0 : ℝ) 1 := ⟨(‖y‖ - a) / (b - a),
      div_nonneg (sub_nonneg.mpr hya') (sub_pos.mpr hab).le,
      (div_le_iff₀ (sub_pos.mpr hab)).mpr (by linarith)⟩
    refine ⟨(z, t), ?_⟩
    change (stereographic' 3 P).symm
      ((a + (b - a) * ((‖y‖ - a) / (b - a))) • (‖y‖⁻¹ • y)) = _
    have hr : a + (b - a) * ((‖y‖ - a) / (b - a)) = ‖y‖ := by
      rw [mul_div_cancel₀ _ (sub_pos.mpr hab).ne']
      ring
    rw [hr, smul_smul, mul_inv_cancel₀ hypos.ne', one_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.range_closedStereographicCylinderMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.range_closedStereographicCylinderMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.range_closedStereographicCylinderMap ``Submission.DifferentialGeometry.Topology.Manifold.range_closedStereographicCylinderMap

def closedStereographicCylinderHomeomorph (P : S3) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) :
    S2 × _root_.Set.Icc (0 : ℝ) 1 ≃ₜ
      ↥((((stereographic' 3 P).symm '' Metric.ball 0 a) ∪
        Neg.neg '' ((stereographic' 3 P).symm '' Metric.ball 0 (4 / b)))ᶜ : Set S3) := by
  have hrange := (range_closedStereographicCylinderMap P ha hab).trans
    (stereographic_double_cap_complement P (ha.trans hab)).symm
  let F := closedStereographicCylinderMap P a b
  let H : S2 × _root_.Set.Icc (0 : ℝ) 1 ≃ₜ _root_.Set.range F :=
    (continuous_closedStereographicCylinderMap P a b).isClosedEmbedding
      (closedStereographicCylinderMap_injective P ha hab) |>.isEmbedding.toHomeomorph
  exact H.trans (Homeomorph.setCongr hrange)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.closedStereographicCylinderHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.closedStereographicCylinderHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.closedStereographicCylinderHomeomorph ``Submission.DifferentialGeometry.Topology.Manifold.closedStereographicCylinderHomeomorph


private def affinePolarDiffeomorph (a b : ℝ) (hab : a < b) :
    Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) (S2 × ℝ) (S2 × ℝ) ∞ where
  toFun p := (-p.1, (a + (b - a) * p.2) / 2)
  invFun p := (-p.1, (2 * p.2 - a) / (b - a))
  left_inv p := by
    refine Prod.ext (neg_neg p.1) ?_
    dsimp only
    field_simp [(sub_pos.mpr hab).ne']
    ring
  right_inv p := by
    refine Prod.ext (neg_neg p.1) ?_
    dsimp only
    rw [mul_div_cancel₀ _ (sub_pos.mpr hab).ne']
    ring
  contMDiff_toFun :=
    ((sphereAntipodalDiffeomorph (E := E3) (n := 2)).contMDiff.comp contMDiff_fst).prodMk
      ((contMDiff_const.add (contMDiff_const.mul contMDiff_snd)).div_const 2)
  contMDiff_invFun :=
    ((sphereAntipodalDiffeomorph (E := E3) (n := 2)).contMDiff.comp contMDiff_fst).prodMk
      ((contMDiff_const.mul contMDiff_snd |>.sub contMDiff_const).div_const (b - a))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.affinePolarDiffeomorph
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.affinePolarDiffeomorph target :: scope.openDecls } }

private def stereographicRadialPartial (P : S3) (a b : ℝ) (hab : a < b) :
    PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (S2 × ℝ) S3 ∞ :=
  ((affinePolarDiffeomorph a b hab).toPartialDiffeomorph.trans
    (DifferentialGeometry.Geometry.Riemannian.euclideanPolarDiffeomorph (E := E3) (n := 2))).trans
      (SphereUnitFilling.sphereChartPartial P)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.stereographicRadialPartial
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.stereographicRadialPartial target :: scope.openDecls } }

private theorem stereographicRadialPartial_apply (P : S3) (a b : ℝ) (hab : a < b)
    (p : S2 × ℝ) :
    stereographicRadialPartial P a b hab p =
      (stereographic' 3 P).symm ((a + (b - a) * p.2) • p.1.val) := by
  change (stereographic' 3 P).symm
    (-((2 : ℝ) • (((a + (b - a) * p.2) / 2) • (-p.1).val))) = _
  congr 1
  change -(2 • (((a + (b - a) * p.2) / 2) • -p.1.val)) = _
  module

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.stereographicRadialPartial_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.stereographicRadialPartial_apply target :: scope.openDecls } }

theorem stereographic_radial_isLocalDiffeomorphAt (P : S3) (a b : ℝ) (hab : a < b)
    (p : S2 × ℝ) (hp : 0 < a + (b - a) * p.2) :
    IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      (fun q : S2 × ℝ => (stereographic' 3 P).symm ((a + (b - a) * q.2) • q.1.val)) p := by
  refine ⟨stereographicRadialPartial P a b hab, ?_, ?_⟩
  · change (p ∈ _root_.Set.univ ∧ 0 < (a + (b - a) * p.2) / 2) ∧ _ ∈ _root_.Set.univ
    exact ⟨⟨mem_univ _, by positivity⟩, _root_.Set.mem_univ _⟩
  · intro q _
    exact (stereographicRadialPartial_apply P a b hab q).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.stereographic_radial_isLocalDiffeomorphAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.stereographic_radial_isLocalDiffeomorphAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.stereographic_radial_isLocalDiffeomorphAt ``Submission.DifferentialGeometry.Topology.Manifold.stereographic_radial_isLocalDiffeomorphAt

theorem contMDiff_closedStereographicCylinderMap (P : S3) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) :
    ContMDiff ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) ∞ (closedStereographicCylinderMap P a b) := by
  intro p
  have hr : 0 < a + (b - a) * p.2.val := by nlinarith [p.2.property.1]
  have h := (stereographic_radial_isLocalDiffeomorphAt P a b hab (p.1, p.2.val) hr).contMDiffAt
  have hp : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (fun q : S2 × _root_.Set.Icc (0 : ℝ) 1 => (q.1, q.2.val)) :=
    contMDiff_fst.prodMk (contMDiff_subtypeVal_Icc.comp contMDiff_snd)
  have hcomp := h.comp p (hp.contMDiffAt (x := p))
  exact hcomp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.contMDiff_closedStereographicCylinderMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.contMDiff_closedStereographicCylinderMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.contMDiff_closedStereographicCylinderMap ``Submission.DifferentialGeometry.Topology.Manifold.contMDiff_closedStereographicCylinderMap

theorem closedStereographicCylinderMap_lower (P : S3) (a b : ℝ) (z : S2) :
    closedStereographicCylinderMap P a b (z, ⟨0, by norm_num⟩) =
      (stereographic' 3 P).symm (a • z.val) := by
  simp [closedStereographicCylinderMap]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.closedStereographicCylinderMap_lower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.closedStereographicCylinderMap_lower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.closedStereographicCylinderMap_lower ``Submission.DifferentialGeometry.Topology.Manifold.closedStereographicCylinderMap_lower

theorem closedStereographicCylinderMap_upper (P : S3) (a b : ℝ) (z : S2) :
    closedStereographicCylinderMap P a b (z, ⟨1, by norm_num⟩) =
      (stereographic' 3 P).symm (b • z.val) := by
  simp [closedStereographicCylinderMap]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.closedStereographicCylinderMap_upper then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.closedStereographicCylinderMap_upper"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.closedStereographicCylinderMap_upper ``Submission.DifferentialGeometry.Topology.Manifold.closedStereographicCylinderMap_upper

end DifferentialGeometry.Topology.Manifold
