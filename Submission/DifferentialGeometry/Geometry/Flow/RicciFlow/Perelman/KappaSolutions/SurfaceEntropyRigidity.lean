import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceEntropyBasic
import Mathlib.Topology.Order.MonotoneConvergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Filter _root_.Set
open scoped _root_.Topology _root_.Submission.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M] [Nonempty M]

theorem surfaceEntropy_rigidity_of_backward_minimum
    (g : ℝ → SmoothRiemannianMetric I M) (C : ℝ)
    (hC : ∀ t : ℝ, t ≤ 0 → totalScalarCurvature (g t) = C)
    (hpositive : ∀ t : ℝ, t ≤ 0 → ∀ x : M, 0 < metricScalarAt (I := I) (g t) x)
    (hmono : AntitoneOn (fun t => surfaceEntropy (g t)) (_root_.Set.Iic (0 : ℝ)))
    (tau : ℕ → ℝ) (htau : _root_.Filter.Tendsto tau _root_.Filter.atTop _root_.Filter.atTop)
    (hbackward : _root_.Filter.Tendsto (fun n => surfaceEntropy (g (-tau n)))
      _root_.Filter.atTop (𝓝 (C * Real.log C))) :
    ∀ t : ℝ, t ≤ 0 → surfaceEntropy (g t) = C * Real.log C ∧
      ∃ c : ℝ, ∀ x : M, metricScalarAt (I := I) (g t) x = c := by
  intro t ht
  have hminimum := surfaceEntropy_lower_and_eq_iff_constant (g t) (hpositive t ht)
  rw [hC t ht] at hminimum
  have hupperEventually : ∀ᶠ n in _root_.Filter.atTop,
      surfaceEntropy (g t) ≤ surfaceEntropy (g (-tau n)) := by
    filter_upwards [htau (_root_.Filter.eventually_ge_atTop (-t))] with n hn
    change -t ≤ tau n at hn
    have hnt : -tau n ≤ t := by linarith
    exact hmono (hnt.trans ht) ht hnt
  have hupper : surfaceEntropy (g t) ≤ C * Real.log C :=
    le_of_tendsto_of_tendsto
      (tendsto_const_nhds : _root_.Filter.Tendsto (fun _ : ℕ => surfaceEntropy (g t))
        _root_.Filter.atTop (𝓝 (surfaceEntropy (g t)))) hbackward hupperEventually
  have heq : surfaceEntropy (g t) = C * Real.log C :=
    le_antisymm hupper hminimum.1
  exact ⟨heq, hminimum.2.mp heq⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_rigidity_of_backward_minimum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_rigidity_of_backward_minimum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_rigidity_of_backward_minimum ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_rigidity_of_backward_minimum

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
