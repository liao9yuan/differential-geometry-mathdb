import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SphereUnitFilling
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SphereCapProfileSmooth
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.UnitLaw
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.QuotientTransport
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.TransportDiffeomorphism

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.InnerProductSpace
open _root_.Function

namespace DifferentialGeometry.Topology.SphereUnitFilling

lemma capPoint_boundary (P : S3) (w : Metric.sphere (0 : E3) 1) :
    (capPoint P ((sphereBallChart P).boundaryMap w) : E3) = (2 : ℝ) • (w : E3) := by
  have hw1 : ‖(w : E3)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using w.2
  have hbm : ((sphereBallChart P).boundaryMap w : S3)
      = (stereographic' 3 P).symm (-((2 : ℝ) • (w : E3))) := by
    change (sphereChartPartial P).toPartialEquiv.toFun (w : E3) = _
    rw [sphereChartPartial_toFun]
  have hxne : -((2 : ℝ) • (w : E3)) ≠ 0 := by
    intro h
    have hnorm := congrArg _root_.Norm.norm h
    rw [norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 2), hw1, mul_one, norm_zero] at hnorm
    norm_num at hnorm
  have hanti := DifferentialGeometry.Topology.Manifold.stereographicInverse_antipodal
    (n := 3) (north := P) (x := -((2 : ℝ) • (w : E3))) hxne
  rw [capPoint_apply, hbm, ← hanti]
  rw [(stereographic' 3 P).right_inv (mem_target_stereographic P _)]
  have hxnorm : ‖-((2 : ℝ) • (w : E3))‖ = 2 := by
    rw [norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 2), hw1, mul_one]
  rw [hxnorm]
  norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.capPoint_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.capPoint_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.capPoint_boundary ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.capPoint_boundary

lemma capPoint_radial (P : S3) (w : Metric.sphere (0 : E3) 1) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hr : ρ ∈ Set.Icc 1 2) :
    (capPoint P ((sphereBallChart P).radialMap w ρ hr) : E3) = (2 / ρ) • (w : E3) := by
  have hw1 : ‖(w : E3)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using w.2
  have hρpos : (0 : ℝ) < ρ := by linarith
  have hbm : ((sphereBallChart P).radialMap w ρ hr : S3)
      = (stereographic' 3 P).symm (-((2 : ℝ) • (ρ • (w : E3)))) := by
    change (sphereChartPartial P).toPartialEquiv.toFun (ρ • (w : E3)) = _
    rw [sphereChartPartial_toFun]
  have hxne : -((2 : ℝ) • (ρ • (w : E3))) ≠ 0 := by
    intro h
    have hnorm := congrArg _root_.Norm.norm h
    simp only [norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hρpos, hw1, mul_one,
      norm_zero] at hnorm
    linarith
  have hanti := DifferentialGeometry.Topology.Manifold.stereographicInverse_antipodal
    (n := 3) (north := P) (x := -((2 : ℝ) • (ρ • (w : E3)))) hxne
  rw [capPoint_apply, hbm, ← hanti]
  rw [(stereographic' 3 P).right_inv (mem_target_stereographic P _)]
  have hxnorm : ‖-((2 : ℝ) • (ρ • (w : E3)))‖ = 2 * ρ := by
    simp only [norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hρpos, hw1, mul_one]
  rw [hxnorm]
  have hcoef : (-4 / (2 * ρ) ^ 2) • (-((2 : ℝ) • (ρ • (w : E3)))) = (2 / ρ) • (w : E3) := by
    rw [smul_neg, ← neg_smul, smul_smul, smul_smul]
    congr 1
    field_simp
    ring
  rw [hcoef]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.capPoint_radial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.capPoint_radial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.capPoint_radial ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.capPoint_radial

theorem capRadialMap_capPoint_boundary (P : S3) (z : Metric.sphere (0 : E3) 1) :
    capRadialMap (capPoint P ((sphereBallChart P).boundaryMap (sphereAnti z))) = (z : E3) := by
  rw [capPoint_boundary]
  have hneg : (sphereAnti z : E3) = -(z : E3) := by
    rw [sphereAnti_eq_neg]
    rfl
  rw [hneg]
  have hz : ‖(-(z : E3))‖ = 1 := by
    rw [norm_neg]
    simpa only [Metric.mem_sphere, dist_zero_right] using z.2
  rw [capRadialMap_two_smul hz, neg_neg]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.capRadialMap_capPoint_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.capRadialMap_capPoint_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.capRadialMap_capPoint_boundary ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.capRadialMap_capPoint_boundary

theorem capRadialMap_capPoint_radialRightClamp (P : S3) (z : Metric.sphere (0 : E3) 1)
    (p : ConnectedSumQuotient.CollarDomain) (hp : (p.2 : ℝ) < 0) :
    capRadialMap (capPoint P
        (ConnectedSumQuotient.radialRightClamp (sphereBallChart P) (sphereAnti z) p)) =
      (1 + (p.2 : ℝ)) • (z : E3) := by
  have ht1 : (p.2 : ℝ) < 1 / 2 := p.2.2.2
  have ht2 : -(1 / 2 : ℝ) < (p.2 : ℝ) := p.2.2.1
  have h1 : (1 : ℝ) ≤ 1 - (p.2 : ℝ) := by linarith
  have h2 : 1 - (p.2 : ℝ) ≤ 3 / 2 := by linarith
  have hr : 1 - (p.2 : ℝ) ∈ Set.Icc (1 : ℝ) 2 := ⟨h1, by linarith⟩
  rw [ConnectedSumQuotient.radialRightClamp_of_neg (sphereBallChart P) (sphereAnti z) p hp]
  rw [capPoint_radial P (sphereAnti z) h1 hr]
  have hz : ‖((sphereAnti z : Metric.sphere (0 : E3) 1) : E3)‖ = 1 := by
    have hneg : (sphereAnti z : E3) = -(z : E3) := by
      rw [sphereAnti_eq_neg]
      rfl
    rw [hneg, norm_neg]
    simpa only [Metric.mem_sphere, dist_zero_right] using z.2
  rw [capRadialMap_two_div_smul_of_le hz h1 h2]
  have hneg : (sphereAnti z : E3) = -(z : E3) := by
    rw [sphereAnti_eq_neg]
    rfl
  rw [hneg]
  module

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.capRadialMap_capPoint_radialRightClamp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.capRadialMap_capPoint_radialRightClamp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.capRadialMap_capPoint_radialRightClamp ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.capRadialMap_capPoint_radialRightClamp

lemma capPoint_surjective (P : S3) : Function.Surjective (capPoint P) := by
  rintro ⟨v, hv⟩
  have hv' : ‖v‖ ≤ 2 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hv
  have hmem : (-((stereographic' 3 P).symm v) : S3) ∉
      (sphereBallChart P).chart '' Metric.ball (0 : E3) 1 := by
    refine (not_mem_chart_ball_iff P _).mpr ?_
    have hcoe : ((-((stereographic' 3 P).symm v) : S3) : E4) =
        -(((stereographic' 3 P).symm v : S3) : E4) := by simp
    rw [hcoe, inner_neg_left, inner_stereographic_symm_apply]
    have hden : (0 : ℝ) < ‖v‖ ^ 2 + 4 := by nlinarith [sq_nonneg ‖v‖]
    have hnum : ‖v‖ ^ 2 - 4 ≤ 0 := by nlinarith [norm_nonneg v]
    have hq := div_nonpos_of_nonpos_of_nonneg hnum (le_of_lt hden)
    linarith
  refine ⟨⟨-((stereographic' 3 P).symm v), hmem⟩, Subtype.ext ?_⟩
  rw [capPoint_apply]
  have harg : (-(↑(⟨-((stereographic' 3 P).symm v), hmem⟩ :
      (sphereBallChart P).Punctured) : S3) : S3) = (stereographic' 3 P).symm v := by simp
  rw [harg]
  exact (stereographic' 3 P).right_inv (mem_target_stereographic P v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.capPoint_surjective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.capPoint_surjective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.capPoint_surjective ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.capPoint_surjective

lemma neg_mem_compl_of_mem_punctured (P : S3) (x : (sphereBallChart P).Punctured) :
    (-(x : S3) : S3) ∈ ({P}ᶜ : Set S3) := by
  intro hx
  have hcap : 0 ≤ ⟪((x : S3) : E4), (P : E4)⟫_ℝ :=
    (not_mem_chart_ball_iff P (x : S3)).mp x.2
  have hneg : ⟪((-((x : S3)) : S3) : E4), (P : E4)⟫_ℝ ≤ 0 := by
    have hcoe : ((-((x : S3)) : S3) : E4) = -((x : S3) : E4) := by simp
    rw [hcoe, inner_neg_left]
    linarith
  rw [hx, inner_self_eq_norm_sq_to_K, norm_coe_sphere P] at hneg
  norm_num at hneg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.neg_mem_compl_of_mem_punctured then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.neg_mem_compl_of_mem_punctured"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.neg_mem_compl_of_mem_punctured ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.neg_mem_compl_of_mem_punctured

section Fill

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [T2Space M]

def capFillMap (P : S3) (c : BallChart 3 (𝓡 3) M) :
    (sphereBallChart P).Punctured → {x : M // x ∈ c.chart '' Metric.closedBall (0 : E3) 1} :=
  fun x => ⟨c.chart (capRadialMap (capPoint P x)),
    ⟨capRadialMap (capPoint P x), by
      rw [← capRadialMap_image_closedBall]
      exact ⟨_, by simpa only [Metric.mem_closedBall, dist_zero_right] using (capPoint P x).2,
        rfl⟩, rfl⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.capFillMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.capFillMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.capFillMap ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.capFillMap

omit [T2Space M] in
@[simp]
lemma capFillMap_val (P : S3) (c : BallChart 3 (𝓡 3) M)
    (x : (sphereBallChart P).Punctured) :
    (capFillMap P c x : M) = c.chart (capRadialMap (capPoint P x)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.capFillMap_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.capFillMap_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.capFillMap_val ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.capFillMap_val

omit [T2Space M] in
lemma capFillMap_mem (P : S3) (c : BallChart 3 (𝓡 3) M)
    (x : (sphereBallChart P).Punctured) :
    capRadialMap (capPoint P x) ∈ c.chart.source :=
  c.closedBall_one_subset_source (by
    rw [← capRadialMap_image_closedBall]
    exact ⟨_, by simpa only [Metric.mem_closedBall, dist_zero_right] using (capPoint P x).2,
      rfl⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.capFillMap_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.capFillMap_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.capFillMap_mem ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.capFillMap_mem

omit [T2Space M] in
lemma continuous_capFillMap (P : S3) (c : BallChart 3 (𝓡 3) M) :
    Continuous (capFillMap P c) := by
  refine Continuous.subtype_mk ?_ _
  have hcont : Continuous fun x : (sphereBallChart P).Punctured => capRadialMap (capPoint P x) :=
    contDiff_capRadialMap.continuous.comp
      (continuous_subtype_val.comp (continuous_capPoint P))
  exact c.chart.contMDiffOn_toFun.continuousOn.comp_continuous hcont (capFillMap_mem P c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.continuous_capFillMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.continuous_capFillMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.continuous_capFillMap ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.continuous_capFillMap

omit [T2Space M] in
lemma capFillMap_injective (P : S3) (c : BallChart 3 (𝓡 3) M) :
    Function.Injective (capFillMap P c) := by
  intro x y hxy
  have h1 : capRadialMap (capPoint P x) = capRadialMap (capPoint P y) :=
    c.chart.toPartialEquiv.injOn (capFillMap_mem P c x) (capFillMap_mem P c y)
      (congrArg Subtype.val hxy)
  have h2 := capRadialMap_injOn (capPoint P x).2 (capPoint P y).2 h1
  have h3 : (stereographic' 3 P) (-(x : S3)) = (stereographic' 3 P) (-(y : S3)) := by
    rw [capPoint_apply, capPoint_apply] at h2
    exact h2
  have h4 : (-(x : S3) : S3) = -(y : S3) := by
    rw [← (stereographic' 3 P).left_inv
        (mem_source_stereographic P (neg_mem_compl_of_mem_punctured P x)),
      ← (stereographic' 3 P).left_inv
        (mem_source_stereographic P (neg_mem_compl_of_mem_punctured P y)), h3]
  exact Subtype.ext (neg_injective h4)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.capFillMap_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.capFillMap_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.capFillMap_injective ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.capFillMap_injective

omit [T2Space M] in
lemma capFillMap_surjective (P : S3) (c : BallChart 3 (𝓡 3) M) :
    Function.Surjective (capFillMap P c) := by
  rintro ⟨y, w, hw, rfl⟩
  have hw1 : ‖w‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hw
  have hwmem : w ∈ Metric.closedBall (0 : E3) 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hw1
  obtain ⟨v, hv, hvw⟩ := capRadialMap_surjOn hwmem
  obtain ⟨x, hx⟩ := capPoint_surjective P
    ⟨v, by simpa only [Metric.mem_closedBall, dist_zero_right] using hv⟩
  exact ⟨x, Subtype.ext (by rw [capFillMap_val, hx, hvw])⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.capFillMap_surjective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.capFillMap_surjective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.capFillMap_surjective ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.capFillMap_surjective

noncomputable def capFill (P : S3) (c : BallChart 3 (𝓡 3) M) :
    (sphereBallChart P).Punctured ≃ₜ {x : M // x ∈ c.chart '' Metric.closedBall (0 : E3) 1} :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (capFillMap P c)
      ⟨capFillMap_injective P c, capFillMap_surjective P c⟩)
    (continuous_capFillMap P c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.capFill then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.capFill"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.capFill ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.capFill

@[simp]
lemma capFill_apply (P : S3) (c : BallChart 3 (𝓡 3) M)
    (x : (sphereBallChart P).Punctured) :
    capFill P c x = capFillMap P c x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.capFill_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.capFill_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.capFill_apply ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.capFill_apply

theorem capFill_boundary (P : S3) (c : BallChart 3 (𝓡 3) M)
    (z : Metric.sphere (0 : E3) 1) :
    capFill P c ((sphereBallChart P).boundaryMap (sphereAnti z)) =
      ⟨c.chart z, ⟨z, Metric.mem_closedBall.mpr (le_of_eq (Metric.mem_sphere.mp z.2)), rfl⟩⟩ := by
  refine Subtype.ext ?_
  rw [capFill_apply, capFillMap_val, capRadialMap_capPoint_boundary]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.capFill_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.capFill_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.capFill_boundary ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.capFill_boundary

theorem capFill_radialRightClamp (P : S3) (c : BallChart 3 (𝓡 3) M)
    (z : Metric.sphere (0 : E3) 1) (p : ConnectedSumQuotient.CollarDomain)
    (hp : (p.2 : ℝ) < 0) :
    capFill P c (ConnectedSumQuotient.radialRightClamp (sphereBallChart P) (sphereAnti z) p) =
      ⟨c.chart ((1 + (p.2 : ℝ)) • (z : E3)),
        ⟨(1 + (p.2 : ℝ)) • (z : E3), by
          rw [Metric.mem_closedBall, dist_zero_right,
            BallChart.norm_radial z (by linarith [p.2.2.1])]
          linarith [p.2.2.2], rfl⟩⟩ := by
  refine Subtype.ext ?_
  rw [capFill_apply, capFillMap_val, capRadialMap_capPoint_radialRightClamp P z p hp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.capFill_radialRightClamp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.capFill_radialRightClamp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.capFill_radialRightClamp ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.capFill_radialRightClamp

end Fill
end DifferentialGeometry.Topology.SphereUnitFilling

namespace DifferentialGeometry.Topology

namespace ConnectedSumUnit

universe u

variable {M : ConnectedClosedOrientedManifold.{u} 3}

noncomputable def uliftSphereHomeomorph :
    ULift.{u} SphereUnitFilling.S3 ≃ₜ SphereUnitFilling.S3 where
  toFun x := ULift.down x
  invFun x := ULift.up x
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_uliftDown
  continuous_invFun := continuous_uliftUp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumUnit.uliftSphereHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumUnit.uliftSphereHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumUnit.uliftSphereHomeomorph ``Submission.DifferentialGeometry.Topology.ConnectedSumUnit.uliftSphereHomeomorph

@[simp]
theorem uliftSphereHomeomorph_apply (x : ULift.{u} SphereUnitFilling.S3) :
    uliftSphereHomeomorph x = ULift.down x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumUnit.uliftSphereHomeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumUnit.uliftSphereHomeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumUnit.uliftSphereHomeomorph_apply ``Submission.DifferentialGeometry.Topology.ConnectedSumUnit.uliftSphereHomeomorph_apply

theorem puncturedImage_ulift (P : SphereUnitFilling.S3)
    (d : OrientedBallChart standardThreeSphereLift.{u}.toClosedOrientedManifold)
    (hd : ∀ u : csE3, ULift.down (d.toBallChart.chart u)
      = (SphereUnitFilling.sphereBallChart P).chart u) :
    uliftSphereHomeomorph '' (d.toBallChart.chart '' Metric.ball (0 : csE3) 1)
      = (SphereUnitFilling.sphereBallChart P).chart '' Metric.ball (0 : csE3) 1 := by
  ext y
  constructor
  · rintro ⟨x, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨v, hv, (hd v).symm⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨ULift.up ((SphereUnitFilling.sphereBallChart P).chart v),
      ⟨v, hv, ((congrArg ULift.up (hd v).symm).trans (ULift.up_down _)).symm⟩, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumUnit.puncturedImage_ulift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumUnit.puncturedImage_ulift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumUnit.puncturedImage_ulift ``Submission.DifferentialGeometry.Topology.ConnectedSumUnit.puncturedImage_ulift

theorem puncturedHomeomorph_apply_val (P : SphereUnitFilling.S3)
    (d : OrientedBallChart standardThreeSphereLift.{u}.toClosedOrientedManifold)
    (hd : ∀ u : csE3, ULift.down (d.toBallChart.chart u)
      = (SphereUnitFilling.sphereBallChart P).chart u)
    (q : d.toBallChart.Punctured) :
    ((BallChart.puncturedHomeomorphOfImage d.toBallChart
        (SphereUnitFilling.sphereBallChart P) uliftSphereHomeomorph
        (puncturedImage_ulift P d hd) q
      : (SphereUnitFilling.sphereBallChart P).Punctured) : SphereUnitFilling.S3)
      = ULift.down q.1 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumUnit.puncturedHomeomorph_apply_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumUnit.puncturedHomeomorph_apply_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumUnit.puncturedHomeomorph_apply_val ``Submission.DifferentialGeometry.Topology.ConnectedSumUnit.puncturedHomeomorph_apply_val

noncomputable def unitFillingOfSphereChart (P : SphereUnitFilling.S3)
    (d : OrientedBallChart standardThreeSphereLift.{u}.toClosedOrientedManifold)
    (hd : ∀ u : csE3, ULift.down (d.toBallChart.chart u)
      = (SphereUnitFilling.sphereBallChart P).chart u)
    (c : OrientedBallChart M.toClosedOrientedManifold) :
    UnitFilling c d boundaryAttachment where
  fill := (BallChart.puncturedHomeomorphOfImage d.toBallChart
      (SphereUnitFilling.sphereBallChart P) uliftSphereHomeomorph
      (puncturedImage_ulift P d hd)).trans (SphereUnitFilling.capFill P c.toBallChart)
  map_boundary := by
    intro z
    refine Subtype.ext ?_
    rw [Homeomorph.trans_apply]
    have hbd : (BallChart.puncturedHomeomorphOfImage d.toBallChart
          (SphereUnitFilling.sphereBallChart P) uliftSphereHomeomorph
          (puncturedImage_ulift P d hd))
          (d.toBallChart.boundaryMap (boundaryAttachment.1 z))
        = (SphereUnitFilling.sphereBallChart P).boundaryMap
          (SphereUnitFilling.sphereAnti z) := by
      refine Subtype.ext ?_
      rw [puncturedHomeomorph_apply_val P d hd]
      rw [BallChart.boundaryMap_val]
      exact hd (SphereUnitFilling.sphereAnti z)
    rw [hbd]
    exact congrArg Subtype.val
      (SphereUnitFilling.capFill_boundary P c.toBallChart z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumUnit.unitFillingOfSphereChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumUnit.unitFillingOfSphereChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumUnit.unitFillingOfSphereChart ``Submission.DifferentialGeometry.Topology.ConnectedSumUnit.unitFillingOfSphereChart

@[simp]
theorem unitFillingOfSphereChart_fill (P : SphereUnitFilling.S3)
    (d : OrientedBallChart standardThreeSphereLift.{u}.toClosedOrientedManifold)
    (hd : ∀ u : csE3, ULift.down (d.toBallChart.chart u)
      = (SphereUnitFilling.sphereBallChart P).chart u)
    (c : OrientedBallChart M.toClosedOrientedManifold)
    (q : d.toBallChart.Punctured) :
    (unitFillingOfSphereChart P d hd c).fill q
      = (SphereUnitFilling.capFill P c.toBallChart)
        ((BallChart.puncturedHomeomorphOfImage d.toBallChart
          (SphereUnitFilling.sphereBallChart P) uliftSphereHomeomorph
          (puncturedImage_ulift P d hd)) q) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumUnit.unitFillingOfSphereChart_fill then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumUnit.unitFillingOfSphereChart_fill"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumUnit.unitFillingOfSphereChart_fill ``Submission.DifferentialGeometry.Topology.ConnectedSumUnit.unitFillingOfSphereChart_fill

theorem ballComplementCollar_unitFillingOfSphereChart (P : SphereUnitFilling.S3)
    (d : OrientedBallChart standardThreeSphereLift.{u}.toClosedOrientedManifold)
    (hd : ∀ u : csE3, ULift.down (d.toBallChart.chart u)
      = (SphereUnitFilling.sphereBallChart P).chart u)
    (c : OrientedBallChart M.toClosedOrientedManifold) :
    BallComplementCollar (unitFillingOfSphereChart P d hd c) := by
  intro p hp
  have hbd : (BallChart.puncturedHomeomorphOfImage d.toBallChart
        (SphereUnitFilling.sphereBallChart P) uliftSphereHomeomorph
        (puncturedImage_ulift P d hd))
        (ConnectedSumQuotient.radialRightClamp d.toBallChart
          (boundaryAttachment.1 p.1) p)
      = ConnectedSumQuotient.radialRightClamp
          (SphereUnitFilling.sphereBallChart P) (SphereUnitFilling.sphereAnti p.1) p := by
    refine Subtype.ext ?_
    rw [puncturedHomeomorph_apply_val P d hd]
    rw [ConnectedSumQuotient.radialRightClamp_of_neg d.toBallChart
      (boundaryAttachment.1 p.1) p hp]
    rw [ConnectedSumQuotient.radialRightClamp_of_neg
      (SphereUnitFilling.sphereBallChart P) (SphereUnitFilling.sphereAnti p.1) p hp]
    refine (congrArg ULift.down (BallChart.radialMap_val (c := d.toBallChart)
      (boundaryAttachment.1 p.1) (1 - (p.2 : ℝ)) _)).trans ?_
    exact hd _
  rw [unitFillingOfSphereChart_fill P d hd c, hbd]
  exact congrArg Subtype.val
    (SphereUnitFilling.capFill_radialRightClamp P c.toBallChart p.1 p hp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumUnit.ballComplementCollar_unitFillingOfSphereChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumUnit.ballComplementCollar_unitFillingOfSphereChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumUnit.ballComplementCollar_unitFillingOfSphereChart ``Submission.DifferentialGeometry.Topology.ConnectedSumUnit.ballComplementCollar_unitFillingOfSphereChart

end ConnectedSumUnit

end DifferentialGeometry.Topology
