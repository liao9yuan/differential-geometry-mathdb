/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Filter _root_.Topology

namespace Metric
open _root_.Metric

open _root_.Metric in
theorem tendsto_diam_smallSets {X : Type*} [PseudoMetricSpace X] (x : X) :
    Tendsto _root_.Metric.diam (𝓝 x).smallSets (𝓝 (0 : ℝ)) := by
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  refine eventually_smallSets.mpr ⟨closedBall x (ε / 4), _root_.Metric.closedBall_mem_nhds _ (by positivity), ?_⟩
  intro s hs
  rw [Real.dist_eq, sub_zero, abs_of_nonneg Metric.diam_nonneg]
  exact (_root_.Metric.diam_le_of_subset_closedBall (by positivity) hs).trans_lt (by linarith)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Metric.tendsto_diam_smallSets then
    throwError "Refusing to shadow existing declaration Metric.tendsto_diam_smallSets"
  Lean.modifyEnv fun env => Lean.addAlias env `Metric.tendsto_diam_smallSets ``Submission.Metric.tendsto_diam_smallSets

end Metric

open _root_.ContinuousWithinAt in
theorem ContinuousWithinAt.tendsto_diam_image_Icc
    {α X ι : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [PseudoMetricSpace X] {f : α → X} {K : Set α} {x : α}
    (hf : ContinuousWithinAt f K x) {l : Filter ι} {u v : ι → α}
    (hu : _root_.Filter.Tendsto u l (𝓝 x)) (hv : _root_.Filter.Tendsto v l (𝓝 x))
    (hK : ∀ᶠ i in l, _root_.Set.Icc (u i) (v i) ⊆ K) :
    Tendsto (fun i => Metric.diam (f '' _root_.Set.Icc (u i) (v i))) l (𝓝 0) := by
  have hsmall : _root_.Filter.Tendsto (fun i => _root_.Set.Icc (u i) (v i)) l (𝓝[K] x).smallSets := by
    rw [nhdsWithin, _root_.Filter.smallSets_inf, _root_.Filter.smallSets_principal]
    exact tendsto_inf.mpr ⟨hu.Icc hv, tendsto_principal.mpr hK⟩
  exact (Metric.tendsto_diam_smallSets (f x)).comp (hf.image_smallSets.comp hsmall)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ContinuousWithinAt
  let env ← Lean.getEnv
  if env.contains `ContinuousWithinAt.tendsto_diam_image_Icc then
    throwError "Refusing to shadow existing declaration ContinuousWithinAt.tendsto_diam_image_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousWithinAt.tendsto_diam_image_Icc ``Submission.ContinuousWithinAt.tendsto_diam_image_Icc
