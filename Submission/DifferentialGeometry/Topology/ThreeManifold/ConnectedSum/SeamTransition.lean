import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SmoothStructure
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Defs
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SeamOrientation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.TopologicalSpace _root_.Metric
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology
namespace ConnectedSumQuotient

variable {M : Type*} [TopologicalSpace M] [ChartedSpace csModel M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace csModel N]
  [IsManifold (𝓡 3) ∞ N] [T2Space N]
variable (c : BallChart 3 (𝓡 3) M) (d : BallChart 3 (𝓡 3) N) (a : csSphere ≃ₜ csSphere)

def puncturedOfCoord (y : csModel) (hy : y ∈ SeamShell) (h1 : 1 ≤ ‖y‖) : c.Punctured :=
  ⟨c.chart y, by
    rintro ⟨z, hz, heq⟩
    have hzsrc : z ∈ c.chart.source := c.ball_subset_source hz
    have hysrc : y ∈ c.chart.source := by
      apply c.closedBall_subset_source
      rw [Metric.mem_closedBall, dist_zero_right]
      linarith [hy.2]
    have hzy : z = y := c.chart.toPartialEquiv.injOn hzsrc hysrc heq
    have hzn : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz
    rw [hzy] at hzn
    linarith⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.puncturedOfCoord then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.puncturedOfCoord"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.puncturedOfCoord ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.puncturedOfCoord

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] [T2Space M] [T2Space N] in
theorem puncturedOfCoord_val (y : csModel) (hy : y ∈ SeamShell) (h1 : 1 ≤ ‖y‖) :
    (puncturedOfCoord c y hy h1 : M) = c.chart y := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.puncturedOfCoord_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.puncturedOfCoord_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.puncturedOfCoord_val ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.puncturedOfCoord_val

def radialPuncturedOfCoord (y : csModel) (hy : y ∈ SeamShell) (h1 : 1 ≤ ‖y‖) : c.Punctured :=
  c.radialMap (seamDir ⟨y, hy⟩) ‖y‖ ⟨h1, by linarith [hy.2]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.radialPuncturedOfCoord then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.radialPuncturedOfCoord"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.radialPuncturedOfCoord ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.radialPuncturedOfCoord

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] [T2Space M] [T2Space N] in
theorem radialPuncturedOfCoord_val (y : csModel) (hy : y ∈ SeamShell) (h1 : 1 ≤ ‖y‖) :
    (radialPuncturedOfCoord c y hy h1 : M) = c.chart y := by
  have h := radialMap_seamDir_coe c ⟨y, hy⟩ h1
  simpa only [radialPuncturedOfCoord] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.radialPuncturedOfCoord_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.radialPuncturedOfCoord_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.radialPuncturedOfCoord_val ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.radialPuncturedOfCoord_val

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] [T2Space M] [T2Space N] in
theorem puncturedOfCoord_eq_radialPuncturedOfCoord (y : csModel) (hy : y ∈ SeamShell)
    (h1 : 1 ≤ ‖y‖) :
    puncturedOfCoord c y hy h1 = radialPuncturedOfCoord c y hy h1 := by
  apply Subtype.ext
  rw [puncturedOfCoord_val, radialPuncturedOfCoord_val]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.puncturedOfCoord_eq_radialPuncturedOfCoord then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.puncturedOfCoord_eq_radialPuncturedOfCoord"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.puncturedOfCoord_eq_radialPuncturedOfCoord ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.puncturedOfCoord_eq_radialPuncturedOfCoord

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] [T2Space M] [T2Space N] in
theorem seamMap_eq_inl_puncturedOfCoord (y : csModel) (hy : y ∈ SeamShell) (h1 : 1 ≤ ‖y‖) :
    seamMap c d a ⟨y, hy⟩ = inl c d a (puncturedOfCoord c y hy h1) := by
  have h := seamLeft_eq_of_one_le c d a ⟨y, hy⟩ h1
  rw [seamMap_of_one_le c d a ⟨y, hy⟩ h1, h, puncturedOfCoord_eq_radialPuncturedOfCoord c y hy h1]
  congr 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.seamMap_eq_inl_puncturedOfCoord then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.seamMap_eq_inl_puncturedOfCoord"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.seamMap_eq_inl_puncturedOfCoord ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.seamMap_eq_inl_puncturedOfCoord

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] [T2Space M] [T2Space N] in
theorem seamChartX_inl_puncturedOfCoord (y : csModel) (hy : y ∈ SeamShell) (h1 : 1 ≤ ‖y‖) :
    seamChartX c d a (inl c d a (puncturedOfCoord c y hy h1)) = y := by
  rw [← seamMap_eq_inl_puncturedOfCoord c d a y hy h1]
  exact seamChartX_apply_seamMap c d a ⟨y, hy⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.seamChartX_inl_puncturedOfCoord then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.seamChartX_inl_puncturedOfCoord"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.seamChartX_inl_puncturedOfCoord ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.seamChartX_inl_puncturedOfCoord

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] [T2Space M] [T2Space N] in
theorem reflectMap_mem_SeamShell (y : csModel) (hy : y ∈ SeamShell) :
    reflectMap a y ∈ SeamShell := by
  have hnorm : ‖reflectMap a y‖ = 2 - ‖y‖ := norm_reflectMap (by linarith [hy.2])
  rw [SeamShell]
  exact ⟨by rw [hnorm]; linarith [hy.2], by rw [hnorm]; linarith [hy.1]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.reflectMap_mem_SeamShell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.reflectMap_mem_SeamShell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.reflectMap_mem_SeamShell ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.reflectMap_mem_SeamShell

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] [T2Space M] [T2Space N] in
theorem reflectMapInv_mem_SeamShell (y : csModel) (hy : y ∈ SeamShell) :
    reflectMapInv a y ∈ SeamShell := by
  have hnorm : ‖reflectMapInv a y‖ = 2 - ‖y‖ := norm_reflectMapInv (by linarith [hy.2])
  rw [SeamShell]
  exact ⟨by rw [hnorm]; linarith [hy.2], by rw [hnorm]; linarith [hy.1]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.reflectMapInv_mem_SeamShell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.reflectMapInv_mem_SeamShell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.reflectMapInv_mem_SeamShell ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.reflectMapInv_mem_SeamShell

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] [T2Space M] [T2Space N] in
theorem one_le_norm_reflectMap (y : csModel) (hlt : ‖y‖ < 1) :
    1 ≤ ‖reflectMap a y‖ := by
  rw [norm_reflectMap (by linarith)]
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.one_le_norm_reflectMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.one_le_norm_reflectMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.one_le_norm_reflectMap ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.one_le_norm_reflectMap

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] [T2Space M] [T2Space N] in
theorem lt_one_norm_reflectMapInv (y : csModel) (hy : y ∈ SeamShell) (h1 : 1 < ‖y‖) :
    ‖reflectMapInv a y‖ < 1 := by
  rw [norm_reflectMapInv (by linarith [hy.2])]
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.lt_one_norm_reflectMapInv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.lt_one_norm_reflectMapInv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.lt_one_norm_reflectMapInv ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.lt_one_norm_reflectMapInv

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] [T2Space M] [T2Space N] in
theorem seamMap_eq_inr_puncturedOfCoord (y : csModel) (hy : y ∈ SeamShell) (hlt : ‖y‖ < 1) :
    seamMap c d a ⟨y, hy⟩ = inr c d a (puncturedOfCoord d (reflectMap a y)
      (reflectMap_mem_SeamShell a y hy) (one_le_norm_reflectMap a y hlt)) := by
  have h := seamRight_eq_of_lt_one c d a ⟨y, hy⟩ hlt
  rw [seamMap_of_lt_one c d a ⟨y, hy⟩ (by simpa using not_le.mpr hlt), h]
  congr 1
  apply Subtype.ext
  rw [puncturedOfCoord_val]
  exact radialMap_a_seamDir_coe d a ⟨y, hy⟩ hlt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.seamMap_eq_inr_puncturedOfCoord then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.seamMap_eq_inr_puncturedOfCoord"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.seamMap_eq_inr_puncturedOfCoord ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.seamMap_eq_inr_puncturedOfCoord

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] [T2Space M] [T2Space N] in
theorem seamMap_reflectMapInv_eq_inr (y : csModel) (hy : y ∈ SeamShell) (h1 : 1 < ‖y‖) :
    seamMap c d a ⟨reflectMapInv a y, reflectMapInv_mem_SeamShell a y hy⟩ =
      inr c d a (puncturedOfCoord d y hy (le_of_lt h1)) := by
  have hlt : ‖reflectMapInv a y‖ < 1 := lt_one_norm_reflectMapInv a y hy h1
  rw [seamMap_eq_inr_puncturedOfCoord c d a (reflectMapInv a y)
    (reflectMapInv_mem_SeamShell a y hy) hlt]
  congr 1
  apply Subtype.ext
  rw [puncturedOfCoord_val, puncturedOfCoord_val, reflectMap_reflectMapInv a ⟨y, hy⟩]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.seamMap_reflectMapInv_eq_inr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.seamMap_reflectMapInv_eq_inr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.seamMap_reflectMapInv_eq_inr ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.seamMap_reflectMapInv_eq_inr

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] [T2Space M] [T2Space N] in
theorem seamChartX_inr_puncturedOfCoord (y : csModel) (hy : y ∈ SeamShell) (h1 : 1 < ‖y‖) :
    seamChartX c d a (inr c d a (puncturedOfCoord d y hy (le_of_lt h1))) = reflectMapInv a y := by
  rw [← seamMap_reflectMapInv_eq_inr c d a y hy h1]
  exact seamChartX_apply_seamMap c d a ⟨reflectMapInv a y, reflectMapInv_mem_SeamShell a y hy⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.seamChartX_inr_puncturedOfCoord then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.seamChartX_inr_puncturedOfCoord"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.seamChartX_inr_puncturedOfCoord ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.seamChartX_inr_puncturedOfCoord

def leftSeamTransition (y : csModel) : csModel :=
  if h : y ∈ SeamShell ∧ 1 ≤ ‖y‖ then
    seamChartX c d a (inl c d a (puncturedOfCoord c y h.1 h.2))
  else y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.leftSeamTransition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.leftSeamTransition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.leftSeamTransition ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.leftSeamTransition

def rightSeamTransition (y : csModel) : csModel :=
  if h : y ∈ SeamShell ∧ 1 ≤ ‖y‖ then
    seamChartX c d a (inr c d a (puncturedOfCoord d y h.1 h.2))
  else y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.rightSeamTransition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.rightSeamTransition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.rightSeamTransition ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.rightSeamTransition

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] [T2Space M] [T2Space N] in
theorem leftSeamTransition_eventuallyEq (x : csModel) (hx : x ∈ SeamShell) (h1 : 1 < ‖x‖) :
    leftSeamTransition c d a =ᶠ[𝓝 x] id := by
  have hU : {y : csModel | y ∈ SeamShell ∧ 1 < ‖y‖} ∈ 𝓝 x :=
    (isOpen_seamShell.inter (isOpen_lt continuous_const continuous_norm)).mem_nhds ⟨hx, h1⟩
  refine Filter.eventuallyEq_of_mem hU fun y hy => ?_
  rw [leftSeamTransition, dif_pos ⟨hy.1, le_of_lt hy.2⟩]
  exact seamChartX_inl_puncturedOfCoord c d a y hy.1 (le_of_lt hy.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.leftSeamTransition_eventuallyEq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.leftSeamTransition_eventuallyEq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.leftSeamTransition_eventuallyEq ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.leftSeamTransition_eventuallyEq

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] [T2Space M] [T2Space N] in
theorem rightSeamTransition_eventuallyEq (x : csModel) (hx : x ∈ SeamShell) (h1 : 1 < ‖x‖) :
    rightSeamTransition c d a =ᶠ[𝓝 x] reflectMapInv a := by
  have hU : {y : csModel | y ∈ SeamShell ∧ 1 < ‖y‖} ∈ 𝓝 x :=
    (isOpen_seamShell.inter (isOpen_lt continuous_const continuous_norm)).mem_nhds ⟨hx, h1⟩
  refine Filter.eventuallyEq_of_mem hU fun y hy => ?_
  rw [rightSeamTransition, dif_pos ⟨hy.1, le_of_lt hy.2⟩]
  exact seamChartX_inr_puncturedOfCoord c d a y hy.1 hy.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.rightSeamTransition_eventuallyEq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.rightSeamTransition_eventuallyEq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.rightSeamTransition_eventuallyEq ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.rightSeamTransition_eventuallyEq

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] [T2Space M] [T2Space N] in
theorem fderiv_leftSeamTransition (x : csModel) (hx : x ∈ SeamShell) (h1 : 1 < ‖x‖) :
    fderiv ℝ (leftSeamTransition c d a) x = 1 := by
  rw [(leftSeamTransition_eventuallyEq c d a x hx h1).fderiv_eq, fderiv_id]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.fderiv_leftSeamTransition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.fderiv_leftSeamTransition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.fderiv_leftSeamTransition ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.fderiv_leftSeamTransition

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] [T2Space M] [T2Space N] in
theorem fderiv_rightSeamTransition (x : csModel) (hx : x ∈ SeamShell) (h1 : 1 < ‖x‖) :
    fderiv ℝ (rightSeamTransition c d a) x = fderiv ℝ (reflectMapInv a) x := by
  rw [(rightSeamTransition_eventuallyEq c d a x hx h1).fderiv_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.fderiv_rightSeamTransition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.fderiv_rightSeamTransition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.fderiv_rightSeamTransition ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.fderiv_rightSeamTransition

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] [T2Space M] [T2Space N] in
theorem det_fderiv_leftSeamTransition (x : csModel) (hx : x ∈ SeamShell) (h1 : 1 < ‖x‖) :
    LinearMap.det (fderiv ℝ (leftSeamTransition c d a) x : csModel →ₗ[ℝ] csModel) = 1 := by
  rw [fderiv_leftSeamTransition c d a x hx h1]
  exact LinearMap.det_id

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.det_fderiv_leftSeamTransition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.det_fderiv_leftSeamTransition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.det_fderiv_leftSeamTransition ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.det_fderiv_leftSeamTransition

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] [T2Space M] [T2Space N] in
theorem det_fderiv_rightSeamTransition_pos (aD : csSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ csSphere)
    (ha : aD.preservesOrientation (sphereOrientation 2 (by decide))
      (sphereOrientation 2 (by decide)).opposite)
    (x : csModel) (hx : x ∈ SeamShell) (h1 : 1 < ‖x‖) :
    0 < LinearMap.det
      (fderiv ℝ (rightSeamTransition c d aD.toHomeomorph) x : csModel →ₗ[ℝ] csModel) := by
  rw [fderiv_rightSeamTransition c d aD.toHomeomorph x hx h1]
  refine det_fderiv_reflectMapInv_pos aD ha (norm_pos_iff.mpr ?_) (by linarith [hx.2])
  intro h
  rw [h, norm_zero] at h1
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.det_fderiv_rightSeamTransition_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.det_fderiv_rightSeamTransition_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.det_fderiv_rightSeamTransition_pos ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.det_fderiv_rightSeamTransition_pos

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] [T2Space N] in
theorem exists_interiorLeft_eq_seamMap (aD : csSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ csSphere)
    (x : csModel) (hx : x ∈ SeamShell) (h1 : 1 < ‖x‖) :
    ∃ u : c.interior, interiorLeft c d aD u = seamMap c d aD.toHomeomorph ⟨x, hx⟩ := by
  refine ⟨⟨(radialPuncturedOfCoord c x hx (le_of_lt h1) : M),
    radialMap_mem_interior c (z := seamDir ⟨x, hx⟩) ⟨le_of_lt h1, by linarith [hx.2]⟩ h1⟩, ?_⟩
  have key : c.interiorToPunctured ⟨(radialPuncturedOfCoord c x hx (le_of_lt h1) : M),
      radialMap_mem_interior c (z := seamDir ⟨x, hx⟩) ⟨le_of_lt h1, by linarith [hx.2]⟩ h1⟩
      = puncturedOfCoord c x hx (le_of_lt h1) := by
    apply Subtype.ext
    rw [BallChart.interiorToPunctured_val, puncturedOfCoord_val, radialPuncturedOfCoord_val]
  change inl c d aD.toHomeomorph (c.interiorToPunctured _) = seamMap c d aD.toHomeomorph ⟨x, hx⟩
  rw [key, ← seamMap_eq_inl_puncturedOfCoord c d aD.toHomeomorph x hx (le_of_lt h1)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.exists_interiorLeft_eq_seamMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.exists_interiorLeft_eq_seamMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.exists_interiorLeft_eq_seamMap ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.exists_interiorLeft_eq_seamMap

omit [IsManifold (𝓡 3) ∞ M] [T2Space M] [IsManifold (𝓡 3) ∞ N] in
theorem exists_interiorRight_eq_seamMap (aD : csSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ csSphere)
    (x : csModel) (hx : x ∈ SeamShell) (hlt : ‖x‖ < 1) :
    ∃ v : d.interior, interiorRight c d aD v = seamMap c d aD.toHomeomorph ⟨x, hx⟩ := by
  refine ⟨⟨(d.radialMap (aD.toHomeomorph (seamDir ⟨x, hx⟩)) (2 - ‖x‖)
      ⟨by linarith, by linarith [hx.1]⟩ : N),
    radialMap_mem_interior d (z := aD.toHomeomorph (seamDir ⟨x, hx⟩))
      ⟨by linarith, by linarith [hx.1]⟩ (by linarith)⟩, ?_⟩
  have key : d.interiorToPunctured ⟨(d.radialMap (aD.toHomeomorph (seamDir ⟨x, hx⟩)) (2 - ‖x‖)
      ⟨by linarith, by linarith [hx.1]⟩ : N),
      radialMap_mem_interior d (z := aD.toHomeomorph (seamDir ⟨x, hx⟩))
        ⟨by linarith, by linarith [hx.1]⟩ (by linarith)⟩
      = puncturedOfCoord d (reflectMap aD.toHomeomorph x)
        (reflectMap_mem_SeamShell aD.toHomeomorph x hx)
        (one_le_norm_reflectMap aD.toHomeomorph x hlt) := by
    apply Subtype.ext
    rw [BallChart.interiorToPunctured_val, puncturedOfCoord_val,
      radialMap_a_seamDir_coe d aD.toHomeomorph ⟨x, hx⟩ hlt]
  change inr c d aD.toHomeomorph (d.interiorToPunctured _) = seamMap c d aD.toHomeomorph ⟨x, hx⟩
  rw [key, ← seamMap_eq_inr_puncturedOfCoord c d aD.toHomeomorph x hx hlt]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.exists_interiorRight_eq_seamMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.exists_interiorRight_eq_seamMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.exists_interiorRight_eq_seamMap ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.exists_interiorRight_eq_seamMap

end ConnectedSumQuotient

namespace OrientationAssembly

open _root_.Submission.DifferentialGeometry.Topology.ConnectedSumQuotient

universe u

variable {M : ClosedOrientedManifold.{u} 3}

def chartTangentEquiv (c : OrientedBallChart M) {x : csModel} (hx : x ∈ c.chart.source) :
    TangentSpace 𝓘(ℝ, csModel) x ≃L[ℝ] TangentSpace (𝓡 3) (c.chart x) :=
  IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv
    (PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ c.chart hx) (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.OrientationAssembly.chartTangentEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.OrientationAssembly.chartTangentEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.OrientationAssembly.chartTangentEquiv ``Submission.DifferentialGeometry.Topology.OrientationAssembly.chartTangentEquiv

theorem orientation_map_chartTangentEquiv_symm (c : OrientedBallChart M) {x : csModel}
    (hx : x ∈ c.chart.source) :
    Orientation.map (Fin 3) (chartTangentEquiv c hx).toLinearEquiv.symm
        (M.orientation.orientation (c.chart x)) =
      ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.map
        (NormedSpace.fromTangentSpace x).symm.toLinearEquiv).orientation := by
  rw [← c.preserves_orientation x hx]
  exact orientation_map_symm_map _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.OrientationAssembly.orientation_map_chartTangentEquiv_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.OrientationAssembly.orientation_map_chartTangentEquiv_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.OrientationAssembly.orientation_map_chartTangentEquiv_symm ``Submission.DifferentialGeometry.Topology.OrientationAssembly.orientation_map_chartTangentEquiv_symm

end OrientationAssembly
end DifferentialGeometry.Topology
