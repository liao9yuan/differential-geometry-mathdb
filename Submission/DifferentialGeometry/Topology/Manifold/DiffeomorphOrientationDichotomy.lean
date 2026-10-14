import Submission.DifferentialGeometry.Topology.Manifold.OrientationDiffeomorphTransport
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.Instances.Real

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace Diffeomorph
open _root_.Diffeomorph

open _root_.Diffeomorph in
theorem preservesOrientation_or_preservesOrientation_opposite {n : ℕ}
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]
    [PreconnectedSpace N] (f : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ N)
    (oM : DifferentialGeometry.ManifoldOrientation (𝓡 n) M n)
    (oN : DifferentialGeometry.ManifoldOrientation (𝓡 n) N n) :
    f.preservesOrientation oM oN ∨ f.preservesOrientation oM oN.opposite := by
  by_cases h : f.preservesOrientation oM oN
  · exact Or.inl h
  · simp only [Diffeomorph.preservesOrientation] at h
    push Not at h
    obtain ⟨x₀, hx₀⟩ := h
    have hcard : Fintype.card (Fin n) = Module.finrank ℝ (TangentSpace (𝓡 n) (f x₀)) := by
      change Fintype.card (Fin n) = Module.finrank ℝ (EuclideanSpace ℝ (Fin n))
      simp
    have hfin : FiniteDimensional ℝ (TangentSpace (𝓡 n) (f x₀)) :=
      inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin n)))
    have hneg : Orientation.map (Fin n)
        ((f.mfderivToContinuousLinearEquiv (by simp) x₀).toLinearEquiv)
        (oM.orientation x₀) = -oN.orientation (f x₀) :=
      (Orientation.ne_iff_eq_neg _ _ hcard).mp hx₀
    refine Or.inr (Diffeomorph.preservesOrientation_of_eq_at f oM oN.opposite x₀ ?_)
    rw [hneg, DifferentialGeometry.ManifoldOrientation.opposite_orientation]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.preservesOrientation_or_preservesOrientation_opposite then
    throwError "Refusing to shadow existing declaration Diffeomorph.preservesOrientation_or_preservesOrientation_opposite"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.preservesOrientation_or_preservesOrientation_opposite ``Submission.Diffeomorph.preservesOrientation_or_preservesOrientation_opposite

end Diffeomorph
