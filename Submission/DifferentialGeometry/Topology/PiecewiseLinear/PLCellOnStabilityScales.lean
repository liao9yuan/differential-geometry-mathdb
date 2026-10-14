/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnStability

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_core_stability_scales_lt {M₁ M₂ ι : Type*} [TopologicalSpace M₁]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁] [MetricSpace M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] {U : Set M₁} {h : M₁ → M₂}
    (hh : Topology.IsEmbedding (U.domRestrict h)) {C B K : ι → Set M₁}
    (hC : ∀ i, IsPLCellOn 3 (C i) (B i)) (hCU : ∀ i, C i ⊆ U)
    (hK : ∀ i, IsCompact (K i)) (hKC : ∀ i, K i ⊆ C i \ B i)
    {cap : ι → ℝ} (hcap : ∀ i, 0 < cap i) :
    ∃ ε : ι → ℝ, (∀ i, 0 < ε i) ∧ (∀ i, ε i < cap i) ∧
      ∀ i, ∀ F : M₁ → M₂, IsPLHomeomorphInto 3 F (C i) →
        (∀ x ∈ C i, _root_.Dist.dist (h x) (F x) < ε i) → h '' K i ⊆ interior (F '' C i) := by
  have hc : ContinuousOn h U :=
    continuousOn_iff_continuous_domRestrict.mpr hh.continuous
  have hi : _root_.Set.InjOn h U := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hh.injective (show U.domRestrict h ⟨x, hx⟩ =
      U.domRestrict h ⟨y, hy⟩ from hxy))
  have hscale := fun i => exists_dist_lt_image_interior_stable_of_isPLCellOn
    (hC i) (hc.mono (hCU i)) (hi.mono (hCU i)) (hK i) (hKC i)
  choose δ hδ hstable using hscale
  refine ⟨fun i => _root_.Min.min (cap i / 2) (δ i), fun i =>
    lt_min (half_pos (hcap i)) (hδ i), fun i => ?_, ?_⟩
  · exact (min_le_left _ _).trans_lt (half_lt_self (hcap i))
  · intro i F hF hdist
    exact hstable i F hF fun x hx => (hdist x hx).trans_le (min_le_right _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_core_stability_scales_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_core_stability_scales_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_core_stability_scales_lt ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_core_stability_scales_lt

end DifferentialGeometry.Topology.PiecewiseLinear
