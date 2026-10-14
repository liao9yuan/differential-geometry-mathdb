import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegion
import Submission.DifferentialGeometry.Topology.Sequences.NestedSubsequence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Filter _root_.Submission.Filter

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

def DepthExtendable (H : ℕ → ObservedHistory.{u}) (t : ∀ n, _root_.Set.Icc (0 : ℝ) (H n).horizon)
    (y : ∀ n, ((H n).stageAt (t n)).Carrier) (R : ℕ → ℝ) (σ : ℕ → ℕ) (T : ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ i in _root_.Filter.atTop,
    (H (σ i)).isTracedRegion (t (σ i)) (y (σ i)) (A / Real.sqrt (R (σ i))) (T / R (σ i))
      (K * R (σ i))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.DepthExtendable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.DepthExtendable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.DepthExtendable ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.DepthExtendable

variable {H : ℕ → ObservedHistory.{u}} {t : ∀ n, Icc (0 : ℝ) (H n).horizon}
  {y : ∀ n, ((H n).stageAt (t n)).Carrier} {R : ℕ → ℝ} {σ σ' ψ : ℕ → ℕ} {T T' : ℝ}

theorem DepthExtendable.mono_depth (h : DepthExtendable H t y R σ T) (hR : ∀ n, 0 < R n)
    (hT' : 0 < T') (hle : T' ≤ T) : DepthExtendable H t y R σ T' := by
  intro A hA
  obtain ⟨K, hK, hev⟩ := h A hA
  refine ⟨K, hK, hev.mono fun i hi => hi.mono_depth (div_pos hT' (hR (σ i))) ?_⟩
  exact div_le_div_of_nonneg_right hle (hR (σ i)).le

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.DepthExtendable
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.DepthExtendable.mono_depth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.DepthExtendable.mono_depth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.DepthExtendable.mono_depth ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.DepthExtendable.mono_depth

theorem DepthExtendable.comp (h : DepthExtendable H t y R σ T) (hψ : StrictMono ψ) :
    DepthExtendable H t y R (σ ∘ ψ) T := by
  intro A hA
  obtain ⟨K, hK, hev⟩ := h A hA
  exact ⟨K, hK, hψ.tendsto_atTop.eventually hev⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.DepthExtendable.comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.DepthExtendable.comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.DepthExtendable.comp ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.DepthExtendable.comp

theorem DepthExtendable.congr (h : DepthExtendable H t y R σ T)
    (hσ : ∀ᶠ i in _root_.Filter.atTop, σ i = σ' i) : DepthExtendable H t y R σ' T := by
  intro A hA
  obtain ⟨K, hK, hev⟩ := h A hA
  refine ⟨K, hK, ?_⟩
  have key : ∀ m m' : ℕ, m = m' →
      (H m).isTracedRegion (t m) (y m) (A / Real.sqrt (R m)) (T / R m) (K * R m) →
      (H m').isTracedRegion (t m') (y m') (A / Real.sqrt (R m')) (T / R m') (K * R m') := by
    rintro m _ rfl hm
    exact hm
  filter_upwards [hev, hσ] with i hi he
  exact key _ _ he hi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.DepthExtendable.congr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.DepthExtendable.congr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.DepthExtendable.congr ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.DepthExtendable.congr

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
