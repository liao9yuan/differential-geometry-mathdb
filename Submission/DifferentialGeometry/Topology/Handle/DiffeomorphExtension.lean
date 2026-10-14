import Submission.DifferentialGeometry.Topology.Handle.Extension
import Submission.DifferentialGeometry.Topology.Manifold.BallDiffeomorphExtension
import Submission.DifferentialGeometry.Topology.Manifold.InverseFunction
import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph
import Mathlib.Analysis.Normed.Operator.Banach

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Topology.Handle

attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

theorem exists_partialDiffeomorph_extension_closedCell (m : ℕ)
    {u : ClosedCell (m + 1) → EuclideanSpace ℝ (Fin (m + 1))}
    (hu : Manifold.IsSmoothEmbedding (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞ u) :
    ∃ φ : PartialDiffeomorph (𝓡 (m + 1)) (𝓡 (m + 1))
        (EuclideanSpace ℝ (Fin (m + 1))) (EuclideanSpace ℝ (Fin (m + 1))) ∞,
      Metric.closedBall 0 1 ⊆ φ.source ∧ ∀ x : ClosedCell (m + 1), φ x.val = u x := by
  obtain ⟨F, hF, _, hFu, hFd⟩ :=
    exists_contDiff_closedCell_extension_bijective_fderiv m hu.isImmersion
  have hloc : IsLocalDiffeomorphOn (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ F
      (Metric.closedBall 0 1) := by
    intro x
    let y : ClosedCell (m + 1) := ⟨x.val, mem_closedBall_zero_iff.mp x.property⟩
    let A := ContinuousLinearEquiv.ofBijective (fderiv ℝ F x.val)
      (LinearMap.ker_eq_bot.mpr (hFd y).1) (LinearMap.range_eq_top.mpr (hFd y).2)
    exact DifferentialGeometry.Topology.Manifold.isLocalDiffeomorphAt_of_hasMFDerivAt_equiv
      F hF.contMDiff x.val A ((hF.differentiable (by simp) x.val).hasFDerivAt.hasMFDerivAt)
  have hinj : Set.InjOn F (Metric.closedBall 0 1) := by
    intro x hx y hy hxy
    let a : ClosedCell (m + 1) := ⟨x, mem_closedBall_zero_iff.mp hx⟩
    let b : ClosedCell (m + 1) := ⟨y, mem_closedBall_zero_iff.mp hy⟩
    have h : u a = u b := (hFu a).symm.trans (hxy.trans (hFu b))
    exact congrArg Subtype.val (hu.isEmbedding.injective h)
  obtain ⟨φ, hsrc, hφ⟩ :=
    DifferentialGeometry.IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_isCompact
      hloc (_root_.ProperSpace.isCompact_closedBall _ _) ⟨0, Metric.mem_closedBall_self zero_le_one⟩ hinj
  exact ⟨φ, hsrc, fun x => by rw [hφ, hFu x]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.exists_partialDiffeomorph_extension_closedCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.exists_partialDiffeomorph_extension_closedCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.exists_partialDiffeomorph_extension_closedCell ``Submission.DifferentialGeometry.Topology.Handle.exists_partialDiffeomorph_extension_closedCell

theorem exists_diffeomorph_extension_closedCell (m : ℕ)
    {u : ClosedCell (m + 1) → EuclideanSpace ℝ (Fin (m + 1))}
    (hu : Manifold.IsSmoothEmbedding (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞ u) :
    ∃ Φ : EuclideanSpace ℝ (Fin (m + 1)) ≃ₘ[ℝ] EuclideanSpace ℝ (Fin (m + 1)),
      ∀ x : ClosedCell (m + 1), Φ x.val = u x := by
  obtain ⟨φ, hsrc, hφ⟩ := exists_partialDiffeomorph_extension_closedCell m hu
  obtain ⟨Φ, hΦ⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_diffeomorph_eqOn_of_partialDiffeomorph_closedBall
      φ zero_lt_one hsrc
  exact ⟨Φ, fun x => (hΦ (mem_closedBall_zero_iff.mpr x.property)).trans (hφ x)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.exists_diffeomorph_extension_closedCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.exists_diffeomorph_extension_closedCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.exists_diffeomorph_extension_closedCell ``Submission.DifferentialGeometry.Topology.Handle.exists_diffeomorph_extension_closedCell

end DifferentialGeometry.Topology.Handle
