import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Scaling.Parabolic
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Set _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace SolutionOn

def parabolicClosedWindow {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (T Q θ : ℝ) (hQ : 0 < Q) (hθ : 0 ≤ θ) :
    SolutionOn (I := I) (M := M) (RealTimeInterval.closed (-θ) 0 (neg_nonpos.mpr hθ)) where
  base := parabolicFamily S.base T Q hQ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.SolutionOn.parabolicClosedWindow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.SolutionOn.parabolicClosedWindow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.SolutionOn.parabolicClosedWindow ``Submission.DifferentialGeometry.PDE.RicciFlow.SolutionOn.parabolicClosedWindow

@[simp] theorem parabolicClosedWindow_metric {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (T Q θ : ℝ) (hQ : 0 < Q) (hθ : 0 ≤ θ)
    (s : ℝ) :
    (S.parabolicClosedWindow T Q θ hQ hθ).base.metric s =
      scaleMetric Q hQ (S.base.metric (T + s / Q)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.SolutionOn.parabolicClosedWindow_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.SolutionOn.parabolicClosedWindow_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.SolutionOn.parabolicClosedWindow_metric ``Submission.DifferentialGeometry.PDE.RicciFlow.SolutionOn.parabolicClosedWindow_metric

theorem parabolicClosedWindow_metric_zero {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (T Q θ : ℝ) (hQ : 0 < Q) (hθ : 0 ≤ θ) :
    (S.parabolicClosedWindow T Q θ hQ hθ).base.metric 0 =
      scaleMetric Q hQ (S.base.metric T) := by
  simp only [parabolicClosedWindow_metric, zero_div, add_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.SolutionOn.parabolicClosedWindow_metric_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.SolutionOn.parabolicClosedWindow_metric_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.SolutionOn.parabolicClosedWindow_metric_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.SolutionOn.parabolicClosedWindow_metric_zero

end SolutionOn

variable [FiniteDimensional ℝ E] [T2Space M]

theorem isSolutionOn_parabolicClosedWindow {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {T Q θ : ℝ} (hQ : 0 < Q) (hθ : 0 ≤ θ)
    (hcarrier : _root_.Set.Icc (T - θ / Q) T ⊆ D.carrier)
    (hregular : _root_.Set.Ioo (T - θ / Q) T ⊆ D.regular) :
    IsSolutionOn (S.parabolicClosedWindow T Q θ hQ hθ) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  have hT : T ∈ D.carrier := hcarrier ⟨sub_le_self T (div_nonneg hθ hQ.le), le_rfl⟩
  apply isSolutionOn_timeRestrict (parabolicSolution_isSolutionOn S hS T Q hQ hT)
  · intro s hs
    apply hcarrier
    change T - θ / Q ≤ T + s / Q ∧ T + s / Q ≤ T
    have hlo := div_le_div_of_nonneg_right hs.1 hQ.le
    have hhi := div_le_div_of_nonneg_right hs.2 hQ.le
    simp only [neg_div, zero_div] at hlo hhi
    constructor <;> linarith
  · intro s hs
    apply hregular
    change T - θ / Q < T + s / Q ∧ T + s / Q < T
    have hlo := div_lt_div_of_pos_right hs.1 hQ
    have hhi := div_lt_div_of_pos_right hs.2 hQ
    simp only [neg_div, zero_div] at hlo hhi
    constructor <;> linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.isSolutionOn_parabolicClosedWindow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.isSolutionOn_parabolicClosedWindow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.isSolutionOn_parabolicClosedWindow ``Submission.DifferentialGeometry.PDE.RicciFlow.isSolutionOn_parabolicClosedWindow

end DifferentialGeometry.PDE.RicciFlow
