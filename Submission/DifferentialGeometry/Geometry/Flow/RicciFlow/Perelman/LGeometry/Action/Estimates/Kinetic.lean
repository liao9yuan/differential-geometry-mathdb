import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Estimates.CompactCurvature
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Coercivity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.MeasureTheory
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

open _root_.Submission.DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem lRegularizedKinetic_le
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (a b A C : Real) (hab : a ≤ b)
    (hpot : ∀ s ∈ Set.Icc a b,
      C ≤ 2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha s))
    (hkin : IntervalIntegrable (lRegularizedSpeedSq S T alpha) _root_.MeasureTheory.MeasureSpace.volume a b)
    (hLag : IntervalIntegrable (lRegularizedLagrangian S T alpha) _root_.MeasureTheory.MeasureSpace.volume a b)
    (hA : lRegularizedAction S T alpha a b ≤ A) :
    (∫ s in a..b, lRegularizedSpeedSq S T alpha s) ≤
      2 * (A - C * (b - a)) := by
  have hleft : IntervalIntegrable
      (fun s ↦ (1 / 2 : Real) * lRegularizedSpeedSq S T alpha s + C)
      volume a b :=
    (hkin.const_mul (1 / 2 : Real)).add intervalIntegrable_const
  have hmono :
      (∫ s in a..b, (1 / 2 : Real) * lRegularizedSpeedSq S T alpha s + C) ≤
        lRegularizedAction S T alpha a b := by
    unfold lRegularizedAction
    apply intervalIntegral.integral_mono_on hab hleft hLag
    intro s hs
    simpa only [lRegularizedLagrangian, lRegularizedSpeedSq, add_comm] using
      add_le_add_left (hpot s hs)
        ((1 / 2 : Real) * lRegularizedSpeedSq S T alpha s)
  rw [intervalIntegral.integral_add (hkin.const_mul (1 / 2 : Real))
      intervalIntegrable_const,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const] at hmono
  simp only [smul_eq_mul] at hmono
  have hmonoA := hmono.trans hA
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedKinetic_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedKinetic_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedKinetic_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedKinetic_le

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem lRegularizedKinetic_bound
    [CompactSpace M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : ScalarSTContOn (I := I) (M := M) S)
    (T a b A : Real) (hab : a ≤ b)
    (ht : ∀ s ∈ Set.Icc a b, T - s ^ 2 ∈ D.carrier) :
    ∃ C : Real, ∀ alpha : Real → M,
      IntervalIntegrable (lRegularizedSpeedSq S T alpha) _root_.MeasureTheory.MeasureSpace.volume a b →
        IntervalIntegrable (lRegularizedLagrangian S T alpha) _root_.MeasureTheory.MeasureSpace.volume a b →
          lRegularizedAction S T alpha a b ≤ A →
            (∫ s in a..b, lRegularizedSpeedSq S T alpha s) ≤
              2 * (A - C * (b - a)) := by
  obtain ⟨C, hC⟩ := exists_uniform_lower_bound_lRegularizedPotential (I := I) S hS T a b (by
    intro s hs
    exact ht s (by simpa only [Set.uIcc_of_le hab] using hs))
  refine ⟨C, ?_⟩
  intro alpha hkin hLag hA
  exact lRegularizedKinetic_le (I := I) S T alpha a b A C hab
    (fun s hs ↦ hC s (by
      simpa only [Set.uIcc_of_le hab] using hs) (alpha s))
    hkin hLag hA

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedKinetic_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedKinetic_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedKinetic_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedKinetic_bound

end DifferentialGeometry.PDE.RicciFlow.Perelman
