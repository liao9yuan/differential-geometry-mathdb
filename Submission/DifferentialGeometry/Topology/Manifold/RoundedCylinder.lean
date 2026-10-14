/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import Submission.DifferentialGeometry.Topology.Manifold.RoundedStrip
import Submission.DifferentialGeometry.Topology.Manifold.Homeomorph.Transport
import Mathlib.Geometry.Manifold.Instances.Sphere

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Metric _root_.Topology
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Manifold

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

def ballPrismCollar : TopologicalSpace.Opens
    (_root_.Metric.closedBall (0 : E) 1 × _root_.Set.Icc (0 : ℝ) 1) where
  carrier := {p | p.1.val ≠ 0}
  is_open' := isOpen_ne.preimage (continuous_subtype_val.comp continuous_fst)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.ballPrismCollar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.ballPrismCollar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.ballPrismCollar ``Submission.DifferentialGeometry.Manifold.ballPrismCollar

private theorem radial_norm (p : _root_.Metric.sphere (0 : E) 1 × halfOpenStrip) :
    ‖(1 - p.2.val.1) • p.1.val‖ = 1 - p.2.val.1 := by
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_pos (by linarith [p.2.property.2.1]), mem_sphere_zero_iff_norm.mp p.1.property, mul_one]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Manifold.radial_norm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Manifold.radial_norm target :: scope.openDecls } }

noncomputable def ballPrismCollarHomeomorph :
    (_root_.Metric.sphere (0 : E) 1 × halfOpenStrip) ≃ₜ ballPrismCollar E where
  toFun p := ⟨(⟨(1 - p.2.val.1) • p.1.val, by
      rw [mem_closedBall_zero_iff, radial_norm]
      linarith [p.2.property.1]⟩,
    ⟨p.2.val.2, p.2.property.2.2⟩), by
      change (1 - p.2.val.1) • p.1.val ≠ 0
      apply norm_ne_zero_iff.mp
      rw [radial_norm]
      linarith [p.2.property.2.1]⟩
  invFun p := (⟨‖p.val.1.val‖⁻¹ • p.val.1.val,
    mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm p.property)⟩,
    ⟨(1 - ‖p.val.1.val‖, p.val.2.val),
      sub_nonneg.mpr (mem_closedBall_zero_iff.mp p.val.1.property),
      by linarith [norm_pos_iff.mpr p.property], p.val.2.property⟩)
  left_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      change ‖(1 - p.2.val.1) • p.1.val‖⁻¹ • ((1 - p.2.val.1) • p.1.val) = p.1.val
      rw [radial_norm, smul_smul, inv_mul_cancel₀ (by linarith [p.2.property.2.1]), one_smul]
    · apply Subtype.ext
      refine Prod.ext ?_ rfl
      change 1 - ‖(1 - p.2.val.1) • p.1.val‖ = p.2.val.1
      rw [radial_norm]
      ring
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      change (1 - (1 - ‖p.val.1.val‖)) • (‖p.val.1.val‖⁻¹ • p.val.1.val) = p.val.1.val
      rw [sub_sub_cancel, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr p.property), one_smul]
    · rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by
    have hv : Continuous (fun p : ballPrismCollar E => p.val.1.val) := by fun_prop
    have ht : Continuous (fun p : ballPrismCollar E => p.val.2.val) := by fun_prop
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact ((continuous_norm.comp hv).inv₀
        (fun p => norm_ne_zero_iff.mpr p.property)).smul hv
    · apply Continuous.subtype_mk
      exact (continuous_const.sub (continuous_norm.comp hv)).prodMk ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.ballPrismCollarHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.ballPrismCollarHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.ballPrismCollarHomeomorph ``Submission.DifferentialGeometry.Manifold.ballPrismCollarHomeomorph

theorem ballPrismCollarHomeomorph_apply (p : _root_.Metric.sphere (0 : E) 1 × halfOpenStrip) :
    (ballPrismCollarHomeomorph E p).val.1.val = (1 - p.2.val.1) • p.1.val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.ballPrismCollarHomeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.ballPrismCollarHomeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.ballPrismCollarHomeomorph_apply ``Submission.DifferentialGeometry.Manifold.ballPrismCollarHomeomorph_apply

theorem ballPrismCollarHomeomorph_symm_radial (p : ballPrismCollar E) :
    ((ballPrismCollarHomeomorph E).symm p).2.val.1 = 1 - ‖p.val.1.val‖ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.ballPrismCollarHomeomorph_symm_radial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.ballPrismCollarHomeomorph_symm_radial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.ballPrismCollarHomeomorph_symm_radial ``Submission.DifferentialGeometry.Manifold.ballPrismCollarHomeomorph_symm_radial

theorem ballPrismCollarHomeomorph_symm_height (p : ballPrismCollar E) :
    ((ballPrismCollarHomeomorph E).symm p).2.val.2 = p.val.2.val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.ballPrismCollarHomeomorph_symm_height then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.ballPrismCollarHomeomorph_symm_height"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.ballPrismCollarHomeomorph_symm_height ``Submission.DifferentialGeometry.Manifold.ballPrismCollarHomeomorph_symm_height

theorem ballPrismCollarHomeomorph_attaching_iff (p : ballPrismCollar E) :
    p.val.1.val ∈ _root_.Metric.sphere (0 : E) 1 ↔
      ((ballPrismCollarHomeomorph E).symm p).2.val.1 = 0 := by
  rw [mem_sphere_zero_iff_norm, ballPrismCollarHomeomorph_symm_radial, sub_eq_zero]
  exact eq_comm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.ballPrismCollarHomeomorph_attaching_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.ballPrismCollarHomeomorph_attaching_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.ballPrismCollarHomeomorph_attaching_iff ``Submission.DifferentialGeometry.Manifold.ballPrismCollarHomeomorph_attaching_iff

@[instance_reducible]
noncomputable def ballPrismCollarChartedSpace (n : ℕ) :
    ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace 2))
      (ballPrismCollar (EuclideanSpace ℝ (Fin (n + 1)))) := by
  let _ := halfOpenStripChartedSpace
  exact Homeomorph.pullbackChartedSpace
    (ballPrismCollarHomeomorph (EuclideanSpace ℝ (Fin (n + 1)))).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.ballPrismCollarChartedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.ballPrismCollarChartedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.ballPrismCollarChartedSpace ``Submission.DifferentialGeometry.Manifold.ballPrismCollarChartedSpace

theorem ballPrismCollar_isManifold (n : ℕ) :
    let _ := ballPrismCollarChartedSpace n
    IsManifold ((𝓡 n).prod (𝓡∂ 2)) ∞
      (ballPrismCollar (EuclideanSpace ℝ (Fin (n + 1)))) := by
  let _ := halfOpenStripChartedSpace
  let _ : IsManifold (𝓡∂ 2) ∞ halfOpenStrip := halfOpenStrip_isManifold
  exact Homeomorph.instIsManifoldPullback
    (ballPrismCollarHomeomorph (EuclideanSpace ℝ (Fin (n + 1)))).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.ballPrismCollar_isManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.ballPrismCollar_isManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.ballPrismCollar_isManifold ``Submission.DifferentialGeometry.Manifold.ballPrismCollar_isManifold

noncomputable def ballPrismCollarDiffeomorph (n : ℕ) :
    let _ := halfOpenStripChartedSpace
    let _ := ballPrismCollarChartedSpace n
    Diffeomorph ((𝓡 n).prod (𝓡∂ 2)) ((𝓡 n).prod (𝓡∂ 2))
      (ballPrismCollar (EuclideanSpace ℝ (Fin (n + 1))))
      (_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 × halfOpenStrip) ∞ := by
  let _ := halfOpenStripChartedSpace
  let _ : IsManifold (𝓡∂ 2) ∞ halfOpenStrip := halfOpenStrip_isManifold
  exact Homeomorph.pullbackDiffeomorph
    (ballPrismCollarHomeomorph (EuclideanSpace ℝ (Fin (n + 1)))).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.ballPrismCollarDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.ballPrismCollarDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.ballPrismCollarDiffeomorph ``Submission.DifferentialGeometry.Manifold.ballPrismCollarDiffeomorph

theorem ballPrismCollar_boundary_iff (n : ℕ)
    (p : ballPrismCollar (EuclideanSpace ℝ (Fin (n + 1)))) :
    let _ := ballPrismCollarChartedSpace n
    p ∈ ((𝓡 n).prod (𝓡∂ 2)).boundary
        (ballPrismCollar (EuclideanSpace ℝ (Fin (n + 1)))) ↔
      p.val.1.val ∈ _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ∨
        p.val.2.val = 0 ∨ p.val.2.val = 1 := by
  let _ := halfOpenStripChartedSpace
  let _ : IsManifold (𝓡∂ 2) ∞ halfOpenStrip := halfOpenStrip_isManifold
  let _ := ballPrismCollarChartedSpace n
  dsimp only
  rw [← (ballPrismCollarDiffeomorph n).preimage_boundary (by simp),
    ModelWithCorners.boundary_of_boundaryless_left]
  change (True ∧ ((ballPrismCollarHomeomorph _).symm p).2 ∈
    (𝓡∂ 2).boundary halfOpenStrip) ↔ _
  have hb := halfOpenStrip_boundary_iff ((ballPrismCollarHomeomorph _).symm p).2
  dsimp only at hb
  rw [true_and, hb, ← ballPrismCollarHomeomorph_attaching_iff]
  simp only [ballPrismCollarHomeomorph_symm_height]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.ballPrismCollar_boundary_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.ballPrismCollar_boundary_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.ballPrismCollar_boundary_iff ``Submission.DifferentialGeometry.Manifold.ballPrismCollar_boundary_iff

noncomputable def ballPrismCollarChart (n : ℕ)
    (v : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (upper : Bool) :
    OpenPartialHomeomorph (ballPrismCollar (EuclideanSpace ℝ (Fin (n + 1))))
      (ModelProd (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace 2)) :=
  (ballPrismCollarHomeomorph _).symm.toOpenPartialHomeomorph.trans
    ((chartAt (EuclideanSpace ℝ (Fin n)) v).prod (halfOpenStripChart upper))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.ballPrismCollarChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.ballPrismCollarChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.ballPrismCollarChart ``Submission.DifferentialGeometry.Manifold.ballPrismCollarChart

theorem ballPrismCollarChart_mem_atlas (n : ℕ)
    (v : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (upper : Bool) :
    let _ := ballPrismCollarChartedSpace n
    ballPrismCollarChart n v upper ∈
      atlas (ModelProd (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace 2))
        (ballPrismCollar (EuclideanSpace ℝ (Fin (n + 1)))) := by
  let _ := halfOpenStripChartedSpace
  refine ⟨_, ?_, rfl⟩
  exact _root_.Set.mem_image2_of_mem (chart_mem_atlas (EuclideanSpace ℝ (Fin n)) v)
    (_root_.Set.mem_range_self upper)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.ballPrismCollarChart_mem_atlas then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.ballPrismCollarChart_mem_atlas"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.ballPrismCollarChart_mem_atlas ``Submission.DifferentialGeometry.Manifold.ballPrismCollarChart_mem_atlas

theorem ballPrismCollarChart_cover (n : ℕ)
    (p : ballPrismCollar (EuclideanSpace ℝ (Fin (n + 1)))) :
    ∃ v : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, ∃ upper : Bool,
      p ∈ (ballPrismCollarChart n v upper).source := by
  let q := (ballPrismCollarHomeomorph _).symm p
  obtain ⟨upper, hu⟩ := halfOpenStripChart_cover q.2
  exact ⟨q.1, upper, trivial, mem_chart_source (EuclideanSpace ℝ (Fin n)) q.1, hu⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.ballPrismCollarChart_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.ballPrismCollarChart_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.ballPrismCollarChart_cover ``Submission.DifferentialGeometry.Manifold.ballPrismCollarChart_cover

theorem ballPrismCollarChart_transition_eq (n : ℕ)
    (v w : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (i j : Bool) :
    (ballPrismCollarChart n v i).symm.trans (ballPrismCollarChart n w j) =
      ((chartAt (EuclideanSpace ℝ (Fin n)) v).symm.trans
        (chartAt (EuclideanSpace ℝ (Fin n)) w)).prod
        ((halfOpenStripChart i).symm.trans (halfOpenStripChart j)) := by
  unfold ballPrismCollarChart
  rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.trans_assoc,
    ← OpenPartialHomeomorph.trans_assoc
      (ballPrismCollarHomeomorph _).symm.toOpenPartialHomeomorph.symm,
    ← _root_.Homeomorph.symm_toOpenPartialHomeomorph,
    ← _root_.Homeomorph.trans_toOpenPartialHomeomorph,
    _root_.Homeomorph.symm_trans_self]
  simp [← OpenPartialHomeomorph.prod_trans]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.ballPrismCollarChart_transition_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.ballPrismCollarChart_transition_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.ballPrismCollarChart_transition_eq ``Submission.DifferentialGeometry.Manifold.ballPrismCollarChart_transition_eq

theorem ballPrismCollarChart_transition_mem (n : ℕ)
    (v w : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (i j : Bool) :
    (ballPrismCollarChart n v i).symm.trans (ballPrismCollarChart n w j) ∈
      contDiffGroupoid ∞ ((𝓡 n).prod (𝓡∂ 2)) := by
  let _ := ballPrismCollarChartedSpace n
  let _ : IsManifold ((𝓡 n).prod (𝓡∂ 2)) ∞
      (ballPrismCollar (EuclideanSpace ℝ (Fin (n + 1)))) := ballPrismCollar_isManifold n
  exact (contDiffGroupoid ∞ ((𝓡 n).prod (𝓡∂ 2))).compatible
    (ballPrismCollarChart_mem_atlas n v i) (ballPrismCollarChart_mem_atlas n w j)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.ballPrismCollarChart_transition_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.ballPrismCollarChart_transition_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.ballPrismCollarChart_transition_mem ``Submission.DifferentialGeometry.Manifold.ballPrismCollarChart_transition_mem

theorem ballPrismCollarChart_attaching_iff (n : ℕ)
    (v : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (i : Bool)
    (p : ballPrismCollar (EuclideanSpace ℝ (Fin (n + 1)))) :
    p.val.1.val ∈ _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ↔
      (ballPrismCollarChart n v i p).2.val 0 = 0 ∧
        (ballPrismCollarChart n v i p).2.val 1 ≤ 0 := by
  rw [ballPrismCollarHomeomorph_attaching_iff]
  exact halfOpenStripChart_attaching_iff _ i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.ballPrismCollarChart_attaching_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.ballPrismCollarChart_attaching_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.ballPrismCollarChart_attaching_iff ``Submission.DifferentialGeometry.Manifold.ballPrismCollarChart_attaching_iff

end DifferentialGeometry.Manifold
