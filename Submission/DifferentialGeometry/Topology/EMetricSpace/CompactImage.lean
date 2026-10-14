import Mathlib.Topology.EMetricSpace.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.ENNReal.Lemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false

noncomputable section

open _root_.Set
open scoped _root_.ENNReal

namespace EMetric

variable {A X : Type*} [TopologicalSpace A] [PseudoEMetricSpace X]

theorem edist_lt_top_of_continuous_of_preconnected
    [PreconnectedSpace A] {f : A → X} (hf : Continuous f) (a b : A) :
    edist (f a) (f b) < ⊤ := by
  let S : Set A := f ⁻¹' Metric.eball (f b) ⊤
  have hcl : IsClopen S :=
    ⟨Metric.isClosed_eball_top.preimage hf, Metric.isOpen_eball.preimage hf⟩
  have hb : b ∈ S := by
    change _root_.EDist.edist (f b) (f b) < ⊤
    simp
  rcases isClopen_iff.mp hcl with hempty | huniv
  · simp only [hempty, _root_.Set.mem_empty_iff_false] at hb
  · have ha : a ∈ S := huniv ▸ _root_.Set.mem_univ a
    exact ha

run_cmd do
  let env ← Lean.getEnv
  if env.contains `EMetric.edist_lt_top_of_continuous_of_preconnected then
    throwError "Refusing to shadow existing declaration EMetric.edist_lt_top_of_continuous_of_preconnected"
  Lean.modifyEnv fun env => Lean.addAlias env `EMetric.edist_lt_top_of_continuous_of_preconnected ``Submission.EMetric.edist_lt_top_of_continuous_of_preconnected

theorem exists_uniform_edist_bound_of_compact_preconnected
    [CompactSpace A] [PreconnectedSpace A] {f : A → X}
    (hf : Continuous f) (a : A) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ b : A, _root_.EDist.edist (f b) (f a) ≤ ENNReal.ofReal R := by
  have hc : Continuous (fun b => _root_.EDist.edist (f b) (f a)) := hf.edist continuous_const
  obtain ⟨b, -, hmax⟩ := isCompact_univ.exists_isMaxOn ⟨a, _root_.Set.mem_univ a⟩ hc.continuousOn
  refine ⟨(_root_.EDist.edist (f b) (f a)).toReal, ENNReal.toReal_nonneg, ?_⟩
  intro c
  rw [ENNReal.ofReal_toReal (edist_lt_top_of_continuous_of_preconnected hf b a).ne]
  exact hmax (_root_.Set.mem_univ c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `EMetric.exists_uniform_edist_bound_of_compact_preconnected then
    throwError "Refusing to shadow existing declaration EMetric.exists_uniform_edist_bound_of_compact_preconnected"
  Lean.modifyEnv fun env => Lean.addAlias env `EMetric.exists_uniform_edist_bound_of_compact_preconnected ``Submission.EMetric.exists_uniform_edist_bound_of_compact_preconnected

end EMetric

end

end
