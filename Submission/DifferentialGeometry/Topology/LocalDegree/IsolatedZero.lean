import Submission.DifferentialGeometry.Topology.LocalDegree.SphereMap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.Filter _root_.Metric _root_.Set
open scoped _root_.Topology
noncomputable section
namespace DifferentialGeometry.LocalDegree
variable {E F : Type*} [PseudoMetricSpace E] [TopologicalSpace F] [Zero F]

structure IsolatingRadius (f : E → F) (x : E) (R : ℝ) : Prop where
  pos : 0 < R
  continuousOn : ContinuousOn f (_root_.Metric.closedBall x R)
  zero_iff : ∀ y ∈ _root_.Metric.closedBall x R, f y = 0 ↔ y = x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.IsolatingRadius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.IsolatingRadius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.IsolatingRadius ``Submission.DifferentialGeometry.LocalDegree.IsolatingRadius


def isolatedZero (f : E → F) (x : E) : Prop :=
  ∃ R, IsolatingRadius f x R

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.isolatedZero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.isolatedZero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.isolatedZero ``Submission.DifferentialGeometry.LocalDegree.isolatedZero

namespace IsolatingRadius

variable {f g : E → F} {x : E} {R : ℝ} (h : IsolatingRadius f x R)

include h


theorem zero : f x = 0 := (h.zero_iff x (_root_.Metric.mem_closedBall_self h.pos.le)).mpr rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.IsolatingRadius.zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.IsolatingRadius.zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.IsolatingRadius.zero ``Submission.DifferentialGeometry.LocalDegree.IsolatingRadius.zero


theorem nonzero (y : E) (hy : y ∈ _root_.Metric.closedBall x R) (hne : y ≠ x) : f y ≠ 0 :=
  mt (h.zero_iff y hy).mp hne

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.IsolatingRadius.nonzero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.IsolatingRadius.nonzero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.IsolatingRadius.nonzero ``Submission.DifferentialGeometry.LocalDegree.IsolatingRadius.nonzero


theorem mono {r : ℝ} (hr : 0 < r) (hrR : r ≤ R) : IsolatingRadius f x r where
  pos := hr
  continuousOn := h.continuousOn.mono (_root_.Metric.closedBall_subset_closedBall hrR)
  zero_iff y hy := h.zero_iff y (_root_.Metric.closedBall_subset_closedBall hrR hy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.IsolatingRadius.mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.IsolatingRadius.mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.IsolatingRadius.mono ``Submission.DifferentialGeometry.LocalDegree.IsolatingRadius.mono


theorem congr (hfg : _root_.Set.EqOn f g (_root_.Metric.closedBall x R)) : IsolatingRadius g x R where
  pos := h.pos
  continuousOn := h.continuousOn.congr hfg.symm
  zero_iff y hy := by rw [← hfg hy]; exact h.zero_iff y hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.IsolatingRadius.congr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.IsolatingRadius.congr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.IsolatingRadius.congr ``Submission.DifferentialGeometry.LocalDegree.IsolatingRadius.congr

end IsolatingRadius

theorem isolatedZero_of_nhds {f : E → F} {x : E} {s : Set E}
    (hs : s ∈ 𝓝 x) (hc : ContinuousOn f s) (hz : f x = 0)
    (hzero : ∀ᶠ y in 𝓝[≠] x, f y ≠ 0) : isolatedZero f x := by
  have hs' : ∀ᶠ y in 𝓝 x, y ∈ s := hs
  have hn := hs'.and (eventually_nhdsWithin_iff.mp hzero)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨ε / 2, ?_⟩
  have hsub : _root_.Metric.closedBall x (ε / 2) ⊆ s ∩ {y | y ≠ x → f y ≠ 0} := by
    intro y hy
    apply hball
    exact (_root_.Metric.closedBall_subset_ball (by linarith)) hy
  exact {
    pos := by positivity
    continuousOn := hc.mono (fun y hy ↦ (hsub hy).1)
    zero_iff := fun y hy ↦ ⟨fun hfy ↦ by
      by_contra hne
      exact (hsub hy).2 hne hfy, fun hyx ↦ hyx ▸ hz⟩ }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.isolatedZero_of_nhds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.isolatedZero_of_nhds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.isolatedZero_of_nhds ``Submission.DifferentialGeometry.LocalDegree.isolatedZero_of_nhds


theorem isolatedZero_congr {f g : E → F} {x : E} (hfg : f =ᶠ[𝓝 x] g) :
    isolatedZero f x ↔ isolatedZero g x := by
  suffices transfer : ∀ {f g : E → F}, f =ᶠ[𝓝 x] g →
      isolatedZero f x → isolatedZero g x from
    ⟨transfer hfg, transfer hfg.symm⟩
  intro f g hfg ⟨R, hR⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hfg
  let r := _root_.Min.min R (ε / 2)
  have hr : 0 < r := lt_min hR.pos (by positivity)
  have hrr : r ≤ R := min_le_left _ _
  refine ⟨r, (hR.mono hr hrr).congr ?_⟩
  intro y hy
  exact hball (_root_.Metric.closedBall_subset_ball (lt_of_le_of_lt (min_le_right _ _)
    (by linarith)) hy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.isolatedZero_congr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.isolatedZero_congr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.isolatedZero_congr ``Submission.DifferentialGeometry.LocalDegree.isolatedZero_congr

end DifferentialGeometry.LocalDegree
