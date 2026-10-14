import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.WeakDual

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Filter _root_.Set
open scoped _root_.InnerProductSpace _root_.RealInnerProductSpace _root_.Topology

namespace DifferentialGeometry.Analysis.InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [TopologicalSpace.SeparableSpace E]

theorem exists_weakly_convergent_subsequence_of_norm_bounded
    {C : ℝ} (u : ℕ → E) (hu : ∀ m, ‖u m‖ ≤ C) :
    ∃ φ : ℕ → ℕ, ∃ v : E, StrictMono φ ∧
      ∀ z, _root_.Filter.Tendsto (fun m => _root_.Inner.inner ℝ (u (φ m)) z) _root_.Filter.atTop
        (𝓝 (_root_.Inner.inner ℝ v z)) := by
  let w : ℕ → WeakDual ℝ E := fun m =>
    StrongDual.toWeakDual (innerSL ℝ (u m))
  let c₀ : StrongDual ℝ E := innerSL ℝ (0 : E)
  have hwmem : ∀ m, w m ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall c₀ C := by
    intro m
    rw [Set.mem_preimage, Metric.mem_closedBall]
    change _root_.Dist.dist
      ((InnerProductSpace.toDualMap ℝ E) (u m))
      ((InnerProductSpace.toDualMap ℝ E) 0) ≤ C
    rw [(InnerProductSpace.toDualMap ℝ E).isometry.dist_eq, dist_zero_right]
    exact hu m
  rcases WeakDual.isSeqCompact_closedBall ℝ E c₀ C hwmem with
    ⟨wLim, _, φ, hφ, hw⟩
  let v : E :=
    (InnerProductSpace.toDual ℝ E).symm (WeakDual.toStrongDual wLim)
  refine ⟨φ, v, hφ, ?_⟩
  intro z
  have heval := (WeakDual.eval_continuous z).continuousAt.tendsto.comp hw
  simpa only [Function.comp_apply, Function.comp_def, w,
    StrongDual.toWeakDual_apply, WeakDual.toStrongDual_apply,
    innerSL_apply_apply, v, InnerProductSpace.toDual_symm_apply] using heval

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.InnerProductSpace.exists_weakly_convergent_subsequence_of_norm_bounded then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.InnerProductSpace.exists_weakly_convergent_subsequence_of_norm_bounded"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.InnerProductSpace.exists_weakly_convergent_subsequence_of_norm_bounded ``Submission.DifferentialGeometry.Analysis.InnerProductSpace.exists_weakly_convergent_subsequence_of_norm_bounded

end DifferentialGeometry.Analysis.InnerProductSpace

end
