import Mathlib.Topology.Instances.ENNReal.Lemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

namespace DifferentialGeometry.Topology

open _root_.Filter
open scoped _root_.ENNReal _root_.Topology

theorem tendsto_edist_of_tendsto_edist_zero
    {ι : Type*} {α : ι → Type*} [∀ i, PseudoEMetricSpace (α i)]
    {l : Filter ι} {a b c d : ∀ i, α i} {z : ℝ≥0∞}
    (ha : _root_.Filter.Tendsto (fun i => _root_.EDist.edist (a i) (b i)) l (𝓝 0))
    (hc : _root_.Filter.Tendsto (fun i => _root_.EDist.edist (c i) (d i)) l (𝓝 0))
    (hd : _root_.Filter.Tendsto (fun i => _root_.EDist.edist (a i) (c i)) l (𝓝 z)) :
    Tendsto (fun i => _root_.EDist.edist (b i) (d i)) l (𝓝 z) := by
  have he : _root_.Filter.Tendsto (fun i => _root_.EDist.edist (a i) (b i) + _root_.EDist.edist (c i) (d i)) l (𝓝 0) := by
    simpa only [add_zero] using ha.add hc
  have hlo := ENNReal.Tendsto.sub hd he (Or.inr ENNReal.zero_ne_top)
  have hhi := hd.add he
  simp only [tsub_zero, add_zero] at hlo hhi
  apply hlo.squeeze hhi
  · intro i
    apply tsub_le_iff_right.mpr
    simpa only [_root_.PseudoEMetricSpace.edist_comm (d i) (c i), add_comm, add_left_comm, add_assoc] using
      edist_triangle4 (a i) (b i) (d i) (c i)
  · intro i
    simpa only [_root_.PseudoEMetricSpace.edist_comm (b i) (a i), add_comm, add_left_comm, add_assoc] using
      edist_triangle4 (b i) (a i) (c i) (d i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.tendsto_edist_of_tendsto_edist_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.tendsto_edist_of_tendsto_edist_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.tendsto_edist_of_tendsto_edist_zero ``Submission.DifferentialGeometry.Topology.tendsto_edist_of_tendsto_edist_zero

end DifferentialGeometry.Topology
