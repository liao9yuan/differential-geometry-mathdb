import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Bounds.Class
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.Galerkin.TameSolution

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Tensor.RSTensor
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.Connection
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral hiding TensorEigenIdx
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

open scoped _root_.Classical in
theorem exists_galerkin_coordinate_solution (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ Ctop B0 B1 ρ P : ℝ} (hδ : δ < 1) (hCtop : 0 ≤ Ctop) (hB0 : 0 ≤ B0)
    (hB1 : 0 ≤ B1) (hρ : 0 < ρ) (hP : 0 < P)
    (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ ≤ P →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ)
    (htame : ∀ u v : lowerState (I := I) (M := M) g₀ 1
        (lowRegularityStateRadius Ctop B1 ρ P),
      ‖boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal u -
          boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal v‖ ≤
        Ctop * lowRegularityOuterRadius Ctop ρ P *
            ‖(u.1 : TensorHs (I := I) (M := M) g₀ 0 2
              (((1 : ℕ) : ℝ) + 2)) - v.1‖ +
          B0 *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
              ((u.1 : TensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2)) - v.1)‖ +
          B1 *
              (‖(u.1 : TensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2))‖ +
                ‖(v.1 : TensorHs (I := I) (M := M) g₀ 0 2
                  (((1 : ℕ) : ℝ) + 2))‖) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
              ((u.1 : TensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2)) - v.1)‖)
    {T : ℝ} (hT : 0 < T) :
    ∃ U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ,
      (∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T)) ∧
      (∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
        ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        HasDerivWithinAt (fun r => U N r i)
          (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i +
            galerkinTameForce (I := I) (M := M) g₀ 1
              (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le
              (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal)
              (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) i)
          (Set.Ici t) t) ∧
      (∀ N, ∀ i, U N 0 i = 0) ∧
      (∀ N, ∀ t, ∀ i, i ∉ eigenIdxFinset (I := I) (M := M) g₀ N →
        U N t i = 0) := by
  classical
  have hRpos : 0 < lowRegularityStateRadius Ctop B1 ρ P :=
    lowRegularityStateRadius_pos hCtop hB1 hρ hP
  have hQnn : 0 ≤ lowRegularityOuterRadius Ctop ρ P :=
    (lowRegularityOuterRadius_pos hCtop hρ hP).le
  have hstep : ∀ N : ℕ,
      ∃ V : ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ,
        (∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
          ContinuousOn (fun t => V t i) (Set.Icc (0 : ℝ) T)) ∧
        (∀ t ∈ Set.Ico (0 : ℝ) T,
          ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
          HasDerivWithinAt (fun r => V r i)
            (-(TensorEigenIdx.lambda (I := I) (M := M) i) * V t i +
              galerkinTameForce (I := I) (M := M) g₀ 1 hRpos.le
                (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal)
                (eigenIdxFinset (I := I) (M := M) g₀ N) (V t) i)
            (Set.Ici t) t) ∧
        (∀ i, V 0 i = 0) ∧
        (∀ t, ∀ i, i ∉ eigenIdxFinset (I := I) (M := M) g₀ N → V t i = 0) := by
    intro N
    have hκ0 : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
    have hκ : ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        1 + TensorEigenIdx.lambda (I := I) (M := M) i ≤ (N : ℝ) + 1 := by
      intro i hi
      rw [mem_eigenIdxFinset] at hi
      linarith
    exact galerkinTameSolutionOne (I := I) (M := M) g₀ 1 hRpos.le
      (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal)
      hCtop hB0 hB1 hQnn htame
      (eigenIdxFinset (I := I) (M := M) g₀ N) hκ0 hκ hT
  choose U hUcont hUderiv hUinit hUsupp using hstep
  exact ⟨U, hUcont, hUderiv, hUinit, hUsupp⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_galerkin_coordinate_solution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_galerkin_coordinate_solution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_galerkin_coordinate_solution ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_galerkin_coordinate_solution

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
