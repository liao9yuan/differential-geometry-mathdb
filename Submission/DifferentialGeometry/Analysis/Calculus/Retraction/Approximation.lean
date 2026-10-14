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
open scoped _root_.ENNReal

namespace DifferentialGeometry.Analysis

variable {F Q : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [PseudoEMetricSpace Q] [CompactSpace Q]



theorem exists_uniform_retraction_radius {e : Q → F} {r : F → Q} {U : Set F}
    (he : Continuous e) (hU : IsOpen U) (heU : _root_.Set.range e ⊆ U)
    (hr : ContinuousOn r U) (hleft : ∀ q, r (e q) = q)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q z, _root_.Dist.dist z (e q) < δ → z ∈ U ∧ _root_.EDist.edist (r z) q < ε := by
  have hS : IsCompact (_root_.Set.range e) := isCompact_range he
  obtain ⟨η, hη, hηU⟩ := hS.exists_cthickening_subset_open hU heU
  obtain ⟨ρ, hρ, hρK⟩ := hS.exists_isCompact_cthickening
  let d := _root_.Min.min η ρ
  have hd : 0 < d := lt_min hη hρ
  let K := _root_.Metric.cthickening d (_root_.Set.range e)
  have hKU : K ⊆ U := (_root_.Metric.cthickening_mono (min_le_left η ρ) _).trans hηU
  have hK : IsCompact K := hρK.of_isClosed_subset _root_.Metric.isClosed_cthickening
    (_root_.Metric.cthickening_mono (min_le_right η ρ) _)
  have hur := hK.uniformContinuousOn_of_continuous (hr.mono hKU)
  obtain ⟨τ, hτ, hτr⟩ := EMetric.uniformContinuousOn_iff.mp hur ε hε
  obtain ⟨a, ha, haτ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hτ
  have ha0 : 0 < (a : ℝ) := by exact_mod_cast ha
  refine ⟨min d (a : ℝ), lt_min hd ha0, ?_⟩
  intro q z hz
  have hzK : z ∈ K := _root_.Metric.mem_cthickening_of_dist_le z (e q) d (_root_.Set.range e)
    (_root_.Set.mem_range_self q) (hz.trans_le (min_le_left _ _)).le
  have hqK : e q ∈ K := _root_.Metric.self_subset_cthickening (_root_.Set.range e) (_root_.Set.mem_range_self q)
  refine ⟨hKU hzK, ?_⟩
  rw [← hleft q]
  apply hτr hzK hqK
  apply lt_trans _ haτ
  rw [edist_dist]
  simpa only [ENNReal.ofReal_coe_nnreal] using
    (ENNReal.ofReal_lt_ofReal_iff ha0).mpr (hz.trans_le (min_le_right _ _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_uniform_retraction_radius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_uniform_retraction_radius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_uniform_retraction_radius ``Submission.DifferentialGeometry.Analysis.exists_uniform_retraction_radius

end DifferentialGeometry.Analysis
