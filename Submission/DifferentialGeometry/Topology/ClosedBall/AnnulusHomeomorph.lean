/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Real

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Metric

namespace DifferentialGeometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def sphereProdIccHomeomorphAnnulus (a b : ℝ) (ha : 0 < a) :
    (_root_.Metric.sphere (0 : E) 1 × _root_.Set.Icc a b) ≃ₜ {x : E | ‖x‖ ∈ _root_.Set.Icc a b} where
  toFun p := ⟨(p.2 : ℝ) • (p.1 : E), by
    change ‖(p.2 : ℝ) • (p.1 : E)‖ ∈ _root_.Set.Icc a b
    have hr : 0 < (p.2 : ℝ) := ha.trans_le p.2.property.1
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hr,
      mem_sphere_zero_iff_norm.mp p.1.property, mul_one] using p.2.property⟩
  invFun x := (⟨‖(x : E)‖⁻¹ • (x : E), by
    exact mem_sphere_zero_iff_norm.mpr
      (norm_smul_inv_norm (norm_ne_zero_iff.mp (ha.trans_le x.property.1).ne'))⟩,
    ⟨‖(x : E)‖, x.property⟩)
  left_inv p := by
    let q : _root_.Metric.sphere (0 : E) 1 × _root_.Set.Ioi (0 : ℝ) :=
      (p.1, ⟨p.2, ha.trans_le p.2.property.1⟩)
    have h := (homeomorphUnitSphereProd E).apply_symm_apply q
    apply Prod.ext
    · apply Subtype.ext
      simpa only [homeomorphUnitSphereProd_apply_fst_coe,
        homeomorphUnitSphereProd_symm_apply_coe, q] using
        congrArg (fun z : _root_.Metric.sphere (0 : E) 1 × _root_.Set.Ioi (0 : ℝ) => (z.1 : E)) h
    · apply Subtype.ext
      simpa only [homeomorphUnitSphereProd_apply_snd_coe,
        homeomorphUnitSphereProd_symm_apply_coe, q] using
        congrArg (fun z : _root_.Metric.sphere (0 : E) 1 × _root_.Set.Ioi (0 : ℝ) => (z.2 : ℝ)) h
  right_inv x := by
    apply Subtype.ext
    let z : ({0}ᶜ : Set E) :=
      ⟨x, norm_ne_zero_iff.mp (ha.trans_le x.property.1).ne'⟩
    simpa only [homeomorphUnitSphereProd_symm_apply_coe,
      homeomorphUnitSphereProd_apply_fst_coe, homeomorphUnitSphereProd_apply_snd_coe, z] using
      congrArg (fun w : ({0}ᶜ : Set E) => (w : E))
        ((homeomorphUnitSphereProd E).symm_apply_apply z)
  continuous_toFun := by
    exact ((continuous_subtype_val.comp continuous_snd).smul
      (continuous_subtype_val.comp continuous_fst)).subtype_mk _
  continuous_invFun := by
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact ((continuous_norm.comp continuous_subtype_val).inv₀
        (fun x => (ha.trans_le x.property.1).ne')).smul continuous_subtype_val
    · exact (continuous_norm.comp continuous_subtype_val).subtype_mk _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereProdIccHomeomorphAnnulus then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereProdIccHomeomorphAnnulus"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereProdIccHomeomorphAnnulus ``Submission.DifferentialGeometry.Topology.sphereProdIccHomeomorphAnnulus

@[simp]
theorem sphereProdIccHomeomorphAnnulus_apply_coe (a b : ℝ) (ha : 0 < a)
    (p : _root_.Metric.sphere (0 : E) 1 × _root_.Set.Icc a b) :
    (sphereProdIccHomeomorphAnnulus a b ha p : E) = (p.2 : ℝ) • (p.1 : E) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereProdIccHomeomorphAnnulus_apply_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereProdIccHomeomorphAnnulus_apply_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereProdIccHomeomorphAnnulus_apply_coe ``Submission.DifferentialGeometry.Topology.sphereProdIccHomeomorphAnnulus_apply_coe

@[simp]
theorem sphereProdIccHomeomorphAnnulus_symm_apply_fst_coe (a b : ℝ) (ha : 0 < a)
    (x : {x : E | ‖x‖ ∈ _root_.Set.Icc a b}) :
    ((sphereProdIccHomeomorphAnnulus a b ha).symm x).1.val = ‖(x : E)‖⁻¹ • (x : E) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereProdIccHomeomorphAnnulus_symm_apply_fst_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereProdIccHomeomorphAnnulus_symm_apply_fst_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereProdIccHomeomorphAnnulus_symm_apply_fst_coe ``Submission.DifferentialGeometry.Topology.sphereProdIccHomeomorphAnnulus_symm_apply_fst_coe

@[simp]
theorem sphereProdIccHomeomorphAnnulus_symm_apply_snd_coe (a b : ℝ) (ha : 0 < a)
    (x : {x : E | ‖x‖ ∈ _root_.Set.Icc a b}) :
    ((sphereProdIccHomeomorphAnnulus a b ha).symm x).2.val = ‖(x : E)‖ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereProdIccHomeomorphAnnulus_symm_apply_snd_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereProdIccHomeomorphAnnulus_symm_apply_snd_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereProdIccHomeomorphAnnulus_symm_apply_snd_coe ``Submission.DifferentialGeometry.Topology.sphereProdIccHomeomorphAnnulus_symm_apply_snd_coe

theorem interior_norm_band {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    interior {x : E | ‖x‖ ∈ _root_.Set.Icc a b} = {x : E | ‖x‖ ∈ _root_.Set.Ioo a b} := by
  have heq : {x : E | ‖x‖ ∈ _root_.Set.Icc a b} = _root_.Metric.closedBall (0 : E) b ∩ (_root_.Metric.ball 0 a)ᶜ := by
    ext x
    simp only [_root_.Set.mem_ofPred_eq, _root_.Set.mem_Icc, _root_.Set.mem_inter_iff, _root_.Metric.mem_closedBall, _root_.Set.mem_compl_iff,
      _root_.Metric.mem_ball, dist_zero_right, not_lt]
    exact and_comm
  rw [heq, interior_inter, interior_closedBall (0 : E) (ha.trans hab).ne',
    interior_compl, closure_ball (0 : E) ha.ne']
  ext x
  simp only [_root_.Set.mem_inter_iff, _root_.Metric.mem_ball, _root_.Set.mem_compl_iff, _root_.Metric.mem_closedBall, dist_zero_right,
    not_le, _root_.Set.mem_ofPred_eq, _root_.Set.mem_Ioo]
  exact and_comm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.interior_norm_band then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.interior_norm_band"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.interior_norm_band ``Submission.DifferentialGeometry.Topology.interior_norm_band

theorem isCompact_norm_band [FiniteDimensional ℝ E] (a b : ℝ) :
    IsCompact {x : E | ‖x‖ ∈ _root_.Set.Icc a b} := by
  apply (_root_.ProperSpace.isCompact_closedBall (0 : E) b).of_isClosed_subset
    (isClosed_Icc.preimage continuous_norm)
  exact fun x hx => mem_closedBall_zero_iff.mpr hx.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isCompact_norm_band then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isCompact_norm_band"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isCompact_norm_band ``Submission.DifferentialGeometry.Topology.isCompact_norm_band

end DifferentialGeometry.Topology
