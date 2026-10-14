import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Instances.Real.Lemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Filter _root_.Topology
open scoped _root_.NNReal

set_option autoImplicit false

namespace DifferentialGeometry

section UniformSpace

variable {X Y : Type*} [TopologicalSpace X] [UniformSpace Y]

theorem equicontinuousAt_of_continuousAt_of_tail
    {F : ℕ → X → Y} {x : X} {N : ℕ}
    (hcont : ∀ n < N, ContinuousAt (F n) x)
    (htail : EquicontinuousAt (fun i : {n : ℕ // N ≤ n} => F i) x) :
    EquicontinuousAt F x := by
  have hpre : EquicontinuousAt (fun i : Fin N => F i) x :=
    equicontinuousAt_finite.mpr (fun i => hcont i i.isLt)
  intro U hU
  filter_upwards [hpre U hU, htail U hU] with y hyPre hyTail n
  rcases lt_or_ge n N with hn | hn
  · exact hyPre ⟨n, hn⟩
  · exact hyTail ⟨n, hn⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.equicontinuousAt_of_continuousAt_of_tail then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.equicontinuousAt_of_continuousAt_of_tail"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.equicontinuousAt_of_continuousAt_of_tail ``Submission.DifferentialGeometry.equicontinuousAt_of_continuousAt_of_tail

end UniformSpace

section MetricSpace

variable {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]

theorem equicontinuousAt_of_eventually_lipschitzOnWith
    {F : ℕ → X → Y} {x : X}
    (hcont : ∀ n, ContinuousAt (F n) x)
    {S : Set X} (hS : S ∈ 𝓝 x) {K : ℝ≥0}
    (hLip : ∀ᶠ n in _root_.Filter.atTop, LipschitzOnWith K (F n) S) :
    EquicontinuousAt F x := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hLip
  apply equicontinuousAt_of_continuousAt_of_tail (N := N)
    (fun n _ => hcont n)
  have hU : UniformEquicontinuousOn (fun i : {n : ℕ // N ≤ n} => F i) S :=
    LipschitzOnWith.uniformEquicontinuousOn _ K (fun i => hN i i.property)
  have hwithin := hU.equicontinuousOn x (mem_of_mem_nhds hS)
  simpa only [EquicontinuousWithinAt, EquicontinuousAt, nhdsWithin_eq_nhds.mpr hS] using hwithin

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.equicontinuousAt_of_eventually_lipschitzOnWith then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.equicontinuousAt_of_eventually_lipschitzOnWith"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.equicontinuousAt_of_eventually_lipschitzOnWith ``Submission.DifferentialGeometry.equicontinuousAt_of_eventually_lipschitzOnWith

theorem equicontinuous_of_eventually_locally_lipschitzOnWith
    {F : ℕ → X → Y} (hcont : ∀ n, Continuous (F n))
    (hLip : ∀ x, ∃ S ∈ 𝓝 x, ∃ K : ℝ≥0,
      ∀ᶠ n in _root_.Filter.atTop, LipschitzOnWith K (F n) S) :
    Equicontinuous F := by
  intro x
  obtain ⟨S, hS, K, hK⟩ := hLip x
  exact equicontinuousAt_of_eventually_lipschitzOnWith
    (fun n => (hcont n).continuousAt) hS hK

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.equicontinuous_of_eventually_locally_lipschitzOnWith then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.equicontinuous_of_eventually_locally_lipschitzOnWith"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.equicontinuous_of_eventually_locally_lipschitzOnWith ``Submission.DifferentialGeometry.equicontinuous_of_eventually_locally_lipschitzOnWith

end MetricSpace

variable {Y : Type*} [PseudoEMetricSpace Y]

theorem equicontinuous_Ico_of_eventually_lipschitzOnWith
    {a b : ℝ} {F : ℕ → Set.Ico a b → Y}
    (hcont : ∀ n, Continuous (F n))
    (hLip : ∀ r ∈ Set.Ioo a b, ∃ K : ℝ≥0,
      ∀ᶠ n in _root_.Filter.atTop, LipschitzOnWith K (F n) {x | (x : ℝ) ≤ r}) :
    Equicontinuous F := by
  apply equicontinuous_of_eventually_locally_lipschitzOnWith hcont
  intro x
  obtain ⟨r, hxr, hrb⟩ := exists_between x.property.2
  obtain ⟨K, hK⟩ := hLip r ⟨x.property.1.trans_lt hxr, hrb⟩
  refine ⟨{y | (y : ℝ) ≤ r}, ?_, K, hK⟩
  have hsmall : {y : Set.Ico a b | (y : ℝ) < r} ∈ 𝓝 x :=
    (isOpen_lt continuous_subtype_val continuous_const).mem_nhds hxr
  exact Filter.mem_of_superset hsmall (fun y hy => le_of_lt (show (y : ℝ) < r from hy))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.equicontinuous_Ico_of_eventually_lipschitzOnWith then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.equicontinuous_Ico_of_eventually_lipschitzOnWith"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.equicontinuous_Ico_of_eventually_lipschitzOnWith ``Submission.DifferentialGeometry.equicontinuous_Ico_of_eventually_lipschitzOnWith

end DifferentialGeometry
