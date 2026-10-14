import Submission.DifferentialGeometry.Topology.Compactness.ConnectedIntersection
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Homeomorph.Lemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

open _root_.Set

namespace Homeomorph
open _root_.Homeomorph

open _root_.Homeomorph in
private theorem denseRange_inclusion_closure
    {E : Type*} [TopologicalSpace E] {s K : Set E} (hclosure : closure s = K) :
    DenseRange (Set.inclusion (subset_closure.trans_eq hclosure) : s → K) := by
  apply (denseRange_inclusion_iff _).mpr
  rw [hclosure]

run_cmd do
  let target := ``Submission.Homeomorph.denseRange_inclusion_closure
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Homeomorph.denseRange_inclusion_closure target :: scope.openDecls } }

open _root_.Homeomorph in
theorem surjective_extension_to_closure
    {E : Type*} [TopologicalSpace E] [T2Space E] {s K : Set E}
    (h : s ≃ₜ s) (hK : IsCompact K) (hclosure : closure s = K)
    (F : C(K, K))
    (hF : ∀ z : s, F (Set.inclusion (subset_closure.trans_eq hclosure) z) =
      Set.inclusion (subset_closure.trans_eq hclosure) (h z)) :
    Function.Surjective F := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let i : s → K := Set.inclusion (subset_closure.trans_eq hclosure)
  have hi : DenseRange i := denseRange_inclusion_closure hclosure
  have hsub : _root_.Set.range i ⊆ _root_.Set.range F := by
    rintro _ ⟨z, rfl⟩
    refine ⟨i (h.symm z), ?_⟩
    exact (hF (h.symm z)).trans (congrArg i (h.apply_symm_apply z))
  have hclosed : IsClosed (_root_.Set.range F) := (isCompact_range F.continuous).isClosed
  intro y
  exact closure_minimal hsub hclosed (hi y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.surjective_extension_to_closure then
    throwError "Refusing to shadow existing declaration Homeomorph.surjective_extension_to_closure"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.surjective_extension_to_closure ``Submission.Homeomorph.surjective_extension_to_closure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {s K : Set E}

open _root_.Homeomorph in
theorem isPreconnected_fiber_extension_to_convex_closure
    (h : s ≃ₜ s) (hs : Convex ℝ s) (hK : IsCompact K) (hclosure : closure s = K)
    (F : C(K, K))
    (hF : ∀ z : s, F (Set.inclusion (subset_closure.trans_eq hclosure) z) =
      Set.inclusion (subset_closure.trans_eq hclosure) (h z)) (y : K) :
    IsPreconnected (F ⁻¹' {y}) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let i : s → K := Set.inclusion (subset_closure.trans_eq hclosure)
  have hi : DenseRange i := denseRange_inclusion_closure hclosure
  let f : K → ℝ := fun x => _root_.Dist.dist (F x) y
  have hf : Continuous f := F.continuous.dist continuous_const
  have hstrict (ε : ℝ) : IsPreconnected {x : K | f x < ε} := by
    have hlens : IsPreconnected ((Subtype.val : s → E) ⁻¹' Metric.ball (y : E) ε) := by
      apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
      rw [Subtype.image_preimage_coe]
      exact (hs.inter (convex_ball (y : E) ε)).isPreconnected
    have hpre : i ⁻¹' {x : K | f x < ε} =
        h ⁻¹' ((Subtype.val : s → E) ⁻¹' Metric.ball (y : E) ε) := by
      ext z
      change _root_.Dist.dist (F (i z)) y < ε ↔ _root_.Dist.dist (h z : E) (y : E) < ε
      rw [hF z]
      rfl
    have hpreconn : IsPreconnected (i ⁻¹' {x : K | f x < ε}) := by
      rw [hpre]
      exact h.isPreconnected_preimage.mpr hlens
    have himage : IsPreconnected (i '' (i ⁻¹' {x : K | f x < ε})) :=
      hpreconn.image i (continuous_inclusion _).continuousOn
    exact himage.subset_closure (_root_.Set.image_preimage_subset _ _)
      (hi.subset_closure_image_preimage_of_isOpen (isOpen_lt hf continuous_const))
  have hzero : IsPreconnected {x : K | f x ≤ 0} :=
    hf.isPreconnected_le_of_isPreconnected_lt (by norm_num : (0 : ℝ) < 1)
      (isClosed_le hf continuous_const).isCompact (fun ε _ => hstrict ε)
  convert hzero using 1
  ext x
  simp only [_root_.Set.mem_preimage, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, f, dist_le_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.isPreconnected_fiber_extension_to_convex_closure then
    throwError "Refusing to shadow existing declaration Homeomorph.isPreconnected_fiber_extension_to_convex_closure"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.isPreconnected_fiber_extension_to_convex_closure ``Submission.Homeomorph.isPreconnected_fiber_extension_to_convex_closure

open _root_.Homeomorph in
theorem isConnected_fiber_extension_to_convex_closure
    (h : s ≃ₜ s) (hs : Convex ℝ s) (hK : IsCompact K) (hclosure : closure s = K)
    (F : C(K, K))
    (hF : ∀ z : s, F (Set.inclusion (subset_closure.trans_eq hclosure) z) =
      Set.inclusion (subset_closure.trans_eq hclosure) (h z)) (y : K) :
    IsConnected (F ⁻¹' {y}) := by
  obtain ⟨x, hx⟩ := h.surjective_extension_to_closure hK hclosure F hF y
  exact ⟨⟨x, hx⟩, h.isPreconnected_fiber_extension_to_convex_closure hs hK hclosure F hF y⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.isConnected_fiber_extension_to_convex_closure then
    throwError "Refusing to shadow existing declaration Homeomorph.isConnected_fiber_extension_to_convex_closure"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.isConnected_fiber_extension_to_convex_closure ``Submission.Homeomorph.isConnected_fiber_extension_to_convex_closure

open _root_.Homeomorph in
theorem isConnected_fiber_extension_to_closedBall
    {c : E} {r : ℝ} (h : Metric.ball c r ≃ₜ Metric.ball c r)
    (hK : IsCompact (Metric.closedBall c r))
    (F : C(Metric.closedBall c r, Metric.closedBall c r))
    (hF : ∀ z : Metric.ball c r, F ⟨z, Metric.ball_subset_closedBall z.2⟩ =
      ⟨h z, Metric.ball_subset_closedBall (h z).2⟩) (y : Metric.closedBall c r) :
    IsConnected (F ⁻¹' {y}) := by
  by_cases hr : r = 0
  · subst r
    let : Subsingleton (Metric.closedBall c (0 : ℝ)) :=
      (Metric.subsingleton_closedBall c le_rfl).coe_sort
    have heq : F ⁻¹' {y} = univ := by
      ext x
      simp only [_root_.Set.mem_preimage, _root_.Set.mem_singleton_iff, _root_.Set.mem_univ, iff_true]
      exact Subsingleton.elim _ _
    rw [heq]
    exact ⟨⟨y, _root_.Set.mem_univ _⟩, isPreconnected_univ⟩
  · exact h.isConnected_fiber_extension_to_convex_closure (convex_ball c r)
      hK (closure_ball c hr) F hF y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.isConnected_fiber_extension_to_closedBall then
    throwError "Refusing to shadow existing declaration Homeomorph.isConnected_fiber_extension_to_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.isConnected_fiber_extension_to_closedBall ``Submission.Homeomorph.isConnected_fiber_extension_to_closedBall

end Homeomorph

end
