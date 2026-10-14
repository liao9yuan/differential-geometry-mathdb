import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Normed.Module.FiniteDimension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Metric

namespace DifferentialGeometry.Analysis

variable {K E F : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [PseudoMetricSpace F]



theorem exists_uniform_superposition_radius {c : K → E} {g : E → F} {U : Set E}
    (hc : Continuous c) (hU : IsOpen U) (hcU : _root_.Set.range c ⊆ U) (hg : ContinuousOn g U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ k z, _root_.Dist.dist z (c k) < δ →
      z ∈ U ∧ _root_.Dist.dist (g z) (g (c k)) < ε := by
  have hS : IsCompact (_root_.Set.range c) := isCompact_range hc
  obtain ⟨η, hη, hηU⟩ := hS.exists_cthickening_subset_open hU hcU
  obtain ⟨ρ, hρ, hρK⟩ := hS.exists_isCompact_cthickening
  let d := _root_.Min.min η ρ
  have hd : 0 < d := lt_min hη hρ
  let A := _root_.Metric.cthickening d (_root_.Set.range c)
  have hAU : A ⊆ U := (_root_.Metric.cthickening_mono (min_le_left η ρ) _).trans hηU
  have hA : IsCompact A := hρK.of_isClosed_subset _root_.Metric.isClosed_cthickening
    (_root_.Metric.cthickening_mono (min_le_right η ρ) _)
  obtain ⟨a, ha, hag⟩ := Metric.uniformContinuousOn_iff.mp
    (hA.uniformContinuousOn_of_continuous (hg.mono hAU)) ε hε
  refine ⟨min d a, lt_min hd ha, fun k z hz => ?_⟩
  have hzA : z ∈ A := _root_.Metric.mem_cthickening_of_dist_le z (c k) d (_root_.Set.range c)
    (_root_.Set.mem_range_self k) (hz.trans_le (min_le_left _ _)).le
  have hkA : c k ∈ A := _root_.Metric.self_subset_cthickening (_root_.Set.range c) (_root_.Set.mem_range_self k)
  exact ⟨hAU hzA, hag z hzA (c k) hkA (hz.trans_le (min_le_right _ _))⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_uniform_superposition_radius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_uniform_superposition_radius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_uniform_superposition_radius ``Submission.DifferentialGeometry.Analysis.exists_uniform_superposition_radius

end DifferentialGeometry.Analysis
