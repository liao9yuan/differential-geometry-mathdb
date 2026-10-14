import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.ContinuousMap _root_.Set _root_.Metric
open scoped _root_.Topology

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

private def complementPointInclusion {K : Set E} {c : E} (hc : c ∈ K) :
    C((Kᶜ : Set E), ({c}ᶜ : Set E)) :=
  ContinuousMap.inclusion (compl_subset_compl.mpr (singleton_subset_iff.mpr hc))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.complementPointInclusion
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.complementPointInclusion target :: scope.openDecls } }

private def radialExpansion (c : E) (r : ℝ) : C(unitInterval × ({c}ᶜ : Set E), E) where
  toFun p := c + (1 + (1 - p.1.val) * r / ‖p.2.val - c‖) • (p.2.val - c)
  continuous_toFun := by
    apply Continuous.add continuous_const
    apply Continuous.smul
    · apply Continuous.add continuous_const
      apply Continuous.div
      · fun_prop
      · fun_prop
      · intro p
        exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr p.2.property)
    · fun_prop

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.radialExpansion
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.radialExpansion target :: scope.openDecls } }

private theorem radialExpansion_norm (c : E) (r : ℝ) (hr : 0 ≤ r)
    (t : unitInterval) (x : ({c}ᶜ : Set E)) :
    ‖radialExpansion c r (t, x) - c‖ = ‖x.val - c‖ + (1 - t.val) * r := by
  have hx : 0 < ‖x.val - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr x.property)
  have hs : 0 ≤ (1 - t.val) * r := mul_nonneg (sub_nonneg.mpr t.property.2) hr
  change ‖(c + (1 + (1 - t.val) * r / ‖x.val - c‖) • (x.val - c)) - c‖ = _
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  field_simp

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.radialExpansion_norm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.radialExpansion_norm target :: scope.openDecls } }

private theorem radialExpansion_one (c : E) (r : ℝ) (x : ({c}ᶜ : Set E)) :
    radialExpansion c r (1, x) = x.val := by
  simp [radialExpansion]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.radialExpansion_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.radialExpansion_one target :: scope.openDecls } }

private theorem radialExpansion_zero_mem_closedBall_complement
    (c : E) (r : ℝ) (hr : 0 ≤ r) (x : ({c}ᶜ : Set E)) :
    radialExpansion c r (0, x) ∈ (_root_.Metric.closedBall c r)ᶜ := by
  simp only [_root_.Set.mem_compl_iff, _root_.Metric.mem_closedBall, dist_eq_norm, not_le]
  rw [radialExpansion_norm c r hr]
  have hx : 0 < ‖x.val - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr x.property)
  change r < ‖x.val - c‖ + (1 - (0 : ℝ)) * r
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.radialExpansion_zero_mem_closedBall_complement
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.radialExpansion_zero_mem_closedBall_complement target :: scope.openDecls } }

private theorem starConvex_radialExpansion_mem_complement
    {K : Set E} {c : E} (hs : StarConvex ℝ c K) (r : ℝ) (hr : 0 ≤ r)
    (t : unitInterval) (x : ({c}ᶜ : Set E)) (hx : x.val ∉ K) :
    radialExpansion c r (t, x) ∈ Kᶜ := by
  let a : ℝ := 1 + (1 - t.val) * r / ‖x.val - c‖
  have ha : 1 ≤ a := by
    dsimp [a]
    exact le_add_of_nonneg_right (div_nonneg
      (mul_nonneg (sub_nonneg.mpr t.property.2) hr) (norm_nonneg _))
  have ha0 : a ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one ha)
  intro h
  have hshrink := hs.add_smul_sub_mem h (inv_nonneg.mpr (zero_le_one.trans ha))
    (inv_le_one_of_one_le₀ ha)
  apply hx
  change c + a⁻¹ • ((c + a • (x.val - c)) - c) ∈ K at hshrink
  have heq : c + a⁻¹ • ((c + a • (x.val - c)) - c) = x.val := by
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ha0, one_smul]
    abel
  exact heq ▸ hshrink

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.starConvex_radialExpansion_mem_complement
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.starConvex_radialExpansion_mem_complement target :: scope.openDecls } }

private def starConvexComplementPush {K : Set E} (c : E) (r : ℝ) (hr : 0 ≤ r)
    (hK : K ⊆ _root_.Metric.closedBall c r) : C(({c}ᶜ : Set E), (Kᶜ : Set E)) := by
  let f : C(({c}ᶜ : Set E), E) :=
    (radialExpansion c r).comp ⟨fun x => ((0 : unitInterval), x),
      continuous_const.prodMk continuous_id⟩
  have hf (x : ({c}ᶜ : Set E)) : f x ∈ Kᶜ :=
    fun hx => radialExpansion_zero_mem_closedBall_complement c r hr x (hK hx)
  exact ⟨fun x => ⟨f x, hf x⟩, f.continuous.subtype_mk hf⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.starConvexComplementPush
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.starConvexComplementPush target :: scope.openDecls } }

private def starConvexComplementHomotopyEquivOfBound {K : Set E} {c : E}
    (hc : c ∈ K) (hs : StarConvex ℝ c K) (r : ℝ) (hr : 0 ≤ r)
    (hK : K ⊆ _root_.Metric.closedBall c r) : (Kᶜ : Set E) ≃ₕ ({c}ᶜ : Set E) where
  toFun := complementPointInclusion hc
  invFun := starConvexComplementPush c r hr hK
  left_inv := by
    refine ⟨⟨⟨fun p => ⟨radialExpansion c r (p.1, complementPointInclusion hc p.2), ?_⟩,
      ?_⟩, ?_, ?_⟩⟩
    · exact starConvex_radialExpansion_mem_complement hs r hr p.1
        (complementPointInclusion hc p.2) p.2.property
    · apply Continuous.subtype_mk
      exact (radialExpansion c r).continuous.comp
        (continuous_fst.prodMk ((complementPointInclusion hc).continuous.comp continuous_snd))
    · intro x
      rfl
    · intro x
      exact Subtype.ext (radialExpansion_one c r _)
  right_inv := by
    refine ⟨⟨⟨fun p => ⟨radialExpansion c r p, ?_⟩, ?_⟩, ?_, ?_⟩⟩
    · change radialExpansion c r p ≠ c
      apply sub_ne_zero.mp
      apply norm_pos_iff.mp
      rw [radialExpansion_norm c r hr]
      exact add_pos_of_pos_of_nonneg (norm_pos_iff.mpr (sub_ne_zero.mpr p.2.property))
        (mul_nonneg (sub_nonneg.mpr p.1.property.2) hr)
    · exact (radialExpansion c r).continuous.subtype_mk _
    · intro x
      rfl
    · intro x
      exact Subtype.ext (radialExpansion_one c r _)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.starConvexComplementHomotopyEquivOfBound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.starConvexComplementHomotopyEquivOfBound target :: scope.openDecls } }

def boundedStarConvexComplementHomotopyEquiv {K : Set E} {c : E}
    (hc : c ∈ K) (hs : StarConvex ℝ c K) (hK : Bornology.IsBounded K) :
    (Kᶜ : Set E) ≃ₕ ({c}ᶜ : Set E) :=
  let r := Classical.choose (hK.subset_closedBall_lt 0 c)
  let hr := Classical.choose_spec (hK.subset_closedBall_lt 0 c)
  starConvexComplementHomotopyEquivOfBound hc hs r (le_of_lt hr.1) hr.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.boundedStarConvexComplementHomotopyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.boundedStarConvexComplementHomotopyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.boundedStarConvexComplementHomotopyEquiv ``Submission.DifferentialGeometry.Topology.boundedStarConvexComplementHomotopyEquiv

theorem boundedStarConvexComplementHomotopyEquiv_toFun {K : Set E} {c : E}
    (hc : c ∈ K) (hs : StarConvex ℝ c K) (hK : Bornology.IsBounded K) :
    (boundedStarConvexComplementHomotopyEquiv hc hs hK).toFun =
      ContinuousMap.inclusion (compl_subset_compl.mpr (singleton_subset_iff.mpr hc)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.boundedStarConvexComplementHomotopyEquiv_toFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.boundedStarConvexComplementHomotopyEquiv_toFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.boundedStarConvexComplementHomotopyEquiv_toFun ``Submission.DifferentialGeometry.Topology.boundedStarConvexComplementHomotopyEquiv_toFun


end DifferentialGeometry.Topology

end
