import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Topology.Piecewise

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section
open _root_.Set _root_.Filter
open scoped _root_.Topology

namespace DifferentialGeometry.Analysis

open scoped _root_.Classical in
theorem continuousOn_piecewise_of_norm_sub_le_boundary_vanishing
    {X Y : Type*} [TopologicalSpace X] [NormedAddCommGroup Y]
    {Ω : Set X} (hΩ : IsOpen Ω) {u f : X → Y} {b : X → ℝ}
    (hu : ContinuousOn u Ω) (hf : ContinuousOn f (closure Ω))
    (hb : ContinuousOn b (closure Ω)) (hb0 : ∀ x ∈ frontier Ω, b x = 0)
    (hbound : ∀ x ∈ Ω, ‖u x - f x‖ ≤ b x) :
    ContinuousOn (Ω.piecewise u f) (closure Ω) := by
  classical
  intro x hx
  by_cases hxΩ : x ∈ Ω
  · have heq : Ω.piecewise u f =ᶠ[𝓝 x] u :=
      (show ∀ᶠ y in 𝓝 x, y ∈ Ω from hΩ.mem_nhds hxΩ).mono (fun y hy => _root_.Set.piecewise_eq_of_mem Ω u f hy)
    exact ((hu x hxΩ).continuousAt (hΩ.mem_nhds hxΩ)).continuousWithinAt.congr_of_eventuallyEq
      (heq.filter_mono inf_le_left) heq.self_of_nhds
  · have hxf : x ∈ frontier Ω := ⟨hx, by simpa only [hΩ.interior_eq] using hxΩ⟩
    have ht : _root_.Filter.Tendsto b (𝓝[closure Ω] x) (𝓝 0) := by
      have hh := hb x hx
      change _root_.Filter.Tendsto b (𝓝[closure Ω] x) (𝓝 (b x)) at hh
      rwa [hb0 x hxf] at hh
    have hzero : _root_.Filter.Tendsto (fun y => Ω.piecewise u f y - f y)
        (𝓝[closure Ω] x) (𝓝 0) := by
      apply squeeze_zero_norm' _ ht
      filter_upwards [self_mem_nhdsWithin] with y hy
      by_cases hyΩ : y ∈ Ω
      · rw [_root_.Set.piecewise_eq_of_mem Ω u f hyΩ]
        exact hbound y hyΩ
      · rw [_root_.Set.piecewise_eq_of_notMem Ω u f hyΩ, sub_self, norm_zero]
        have hyf : y ∈ frontier Ω := ⟨hy, by simpa only [hΩ.interior_eq] using hyΩ⟩
        rw [hb0 y hyf]
    have hh := hzero.add (hf x hx)
    change _root_.Filter.Tendsto (Ω.piecewise u f) (𝓝[closure Ω] x) (𝓝 (Ω.piecewise u f x))
    rw [_root_.Set.piecewise_eq_of_notMem Ω u f hxΩ]
    simpa only [sub_add_cancel, zero_add] using hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.continuousOn_piecewise_of_norm_sub_le_boundary_vanishing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.continuousOn_piecewise_of_norm_sub_le_boundary_vanishing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.continuousOn_piecewise_of_norm_sub_le_boundary_vanishing ``Submission.DifferentialGeometry.Analysis.continuousOn_piecewise_of_norm_sub_le_boundary_vanishing

end DifferentialGeometry.Analysis

end

end
