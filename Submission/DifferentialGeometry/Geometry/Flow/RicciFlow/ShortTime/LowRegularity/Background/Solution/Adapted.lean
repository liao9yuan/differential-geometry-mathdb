import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Background.Solution.Pointwise
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Background.Energy.Absorption

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.Connection
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

def IsAdaptedBackgroundLowRegularitySolution (g₀ g_bg : SmoothRiemannianMetric I M)
    (K : LowRegularityBoundParameters) {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (u : MaximalRegularitySolutionSpace (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      ((1 : ℕ) : ℝ) T)
    (gforce : timeL2
      (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (Rcap Ctop₂ Kr2 Kr1 Kcap : ℝ) : Prop :=
  IsBackgroundLowRegularitySolutionAt (I := I) (M := M) g₀ g_bg K hT hT1 u gforce Rcap ∧
    HasGalerkinEnergyThreeBoundBackground (I := I) (M := M) g₀ g_bg Ctop₂ Kr2 Kr1 Kcap ∧
    ∃ A B : ℝ, HasEnergyLadderAbsorptionConstantsBackground (I := I) (M := M) g₀ g_bg A B ∧
      Ctop₂ * Kcap ≤ A ∧ Kr2 + Kr1 ≤ B ∧
      ∃ ε : ℝ, 0 < ε ∧
        A * (K.threshold / (1 - K.threshold) ^ 2) +
          B * lowRegularityStateRadius K.top K.slope K.outer K.realize + ε < 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedBackgroundLowRegularitySolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedBackgroundLowRegularitySolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedBackgroundLowRegularitySolution ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedBackgroundLowRegularitySolution

namespace IsAdaptedBackgroundLowRegularitySolution

variable {g₀ g_bg : SmoothRiemannianMetric I M} {K : LowRegularityBoundParameters}
  {T Rcap Ctop₂ Kr2 Kr1 Kcap : ℝ} {hT : 0 < T} {hT1 : T ≤ 1}
  {u : MaximalRegularitySolutionSpace (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
    ((1 : ℕ) : ℝ) T}
  {gforce : timeL2
    (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T}

theorem toIsBackgroundLowRegularitySolutionAt
    (h : IsAdaptedBackgroundLowRegularitySolution (I := I) (M := M) g₀ g_bg K hT hT1
      u gforce Rcap Ctop₂ Kr2 Kr1 Kcap) :
    IsBackgroundLowRegularitySolutionAt (I := I) (M := M) g₀ g_bg K hT hT1 u gforce Rcap :=
  h.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedBackgroundLowRegularitySolution.toIsBackgroundLowRegularitySolutionAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedBackgroundLowRegularitySolution.toIsBackgroundLowRegularitySolutionAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedBackgroundLowRegularitySolution.toIsBackgroundLowRegularitySolutionAt ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedBackgroundLowRegularitySolution.toIsBackgroundLowRegularitySolutionAt

theorem toIsBackgroundLowRegularitySolution
    (h : IsAdaptedBackgroundLowRegularitySolution (I := I) (M := M) g₀ g_bg K hT hT1
      u gforce Rcap Ctop₂ Kr2 Kr1 Kcap) :
    IsBackgroundLowRegularitySolution (I := I) (M := M) g₀ g_bg K
      h.toIsBackgroundLowRegularitySolutionAt.bounds hT hT1 u gforce :=
  h.toIsBackgroundLowRegularitySolutionAt.solve

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedBackgroundLowRegularitySolution.toIsBackgroundLowRegularitySolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedBackgroundLowRegularitySolution.toIsBackgroundLowRegularitySolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedBackgroundLowRegularitySolution.toIsBackgroundLowRegularitySolution ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedBackgroundLowRegularitySolution.toIsBackgroundLowRegularitySolution

theorem toHasGalerkinEnergyThreeBoundBackground
    (h : IsAdaptedBackgroundLowRegularitySolution (I := I) (M := M) g₀ g_bg K hT hT1
      u gforce Rcap Ctop₂ Kr2 Kr1 Kcap) :
    HasGalerkinEnergyThreeBoundBackground (I := I) (M := M) g₀ g_bg Ctop₂ Kr2 Kr1 Kcap :=
  h.2.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedBackgroundLowRegularitySolution.toHasGalerkinEnergyThreeBoundBackground then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedBackgroundLowRegularitySolution.toHasGalerkinEnergyThreeBoundBackground"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedBackgroundLowRegularitySolution.toHasGalerkinEnergyThreeBoundBackground ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedBackgroundLowRegularitySolution.toHasGalerkinEnergyThreeBoundBackground

theorem exists_absorption_constants_and_margin
    (h : IsAdaptedBackgroundLowRegularitySolution (I := I) (M := M) g₀ g_bg K hT hT1
      u gforce Rcap Ctop₂ Kr2 Kr1 Kcap) :
    ∃ A B : ℝ, HasEnergyLadderAbsorptionConstantsBackground (I := I) (M := M) g₀ g_bg A B ∧
      Ctop₂ * Kcap ≤ A ∧ Kr2 + Kr1 ≤ B ∧
      ∃ ε : ℝ, 0 < ε ∧
        A * (K.threshold / (1 - K.threshold) ^ 2) +
          B * lowRegularityStateRadius K.top K.slope K.outer K.realize + ε < 1 :=
  h.2.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedBackgroundLowRegularitySolution.exists_absorption_constants_and_margin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedBackgroundLowRegularitySolution.exists_absorption_constants_and_margin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedBackgroundLowRegularitySolution.exists_absorption_constants_and_margin ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedBackgroundLowRegularitySolution.exists_absorption_constants_and_margin

theorem absorb
    (h : IsAdaptedBackgroundLowRegularitySolution (I := I) (M := M) g₀ g_bg K hT hT1
      u gforce Rcap Ctop₂ Kr2 Kr1 Kcap) :
    ∃ ε : ℝ, 0 < ε ∧
      Ctop₂ * (Kcap * (K.threshold / (1 - K.threshold) ^ 2)) +
          Kr2 * lowRegularityStateRadius K.top K.slope K.outer K.realize +
          Kr1 * lowRegularityStateRadius K.top K.slope K.outer K.realize + ε < 1 := by
  obtain ⟨A, B, _hgate, hA, hB, ε, hε, hbudget⟩ := h.exists_absorption_constants_and_margin
  have hR : 0 ≤ lowRegularityStateRadius K.top K.slope K.outer K.realize :=
    (lowRegularityStateRadius_pos K.top_nonneg K.slope_nonneg
      K.outer_pos K.realize_pos).le
  have hdom := energyLadder_absorption_coefficient_le hA hB h.1.threshold_nonneg hR
  exact ⟨ε, hε, by linarith only [hdom, hbudget]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedBackgroundLowRegularitySolution.absorb then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedBackgroundLowRegularitySolution.absorb"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedBackgroundLowRegularitySolution.absorb ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAdaptedBackgroundLowRegularitySolution.absorb

end IsAdaptedBackgroundLowRegularitySolution

theorem adaptedBackground_of_given
    {g₀ g_bg : SmoothRiemannianMetric I M} {K : LowRegularityBoundParameters}
    {T Rcap : ℝ} {hT : 0 < T} {hT1 : T ≤ 1}
    {u : MaximalRegularitySolutionSpace (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      ((1 : ℕ) : ℝ) T}
    {gforce : timeL2
      (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T}
    (hsolve : IsBackgroundLowRegularitySolutionAt (I := I) (M := M) g₀ g_bg K hT hT1
      u gforce Rcap)
    {A B : ℝ} (hgate : HasEnergyLadderAbsorptionConstantsBackground (I := I) (M := M) g₀ g_bg A B)
    (hbudget : ∃ ε : ℝ, 0 < ε ∧
      A * (K.threshold / (1 - K.threshold) ^ 2) +
        B * lowRegularityStateRadius K.top K.slope K.outer K.realize + ε < 1) :
    ∃ Ctop₂ Kr2 Kr1 Kcap : ℝ,
      IsAdaptedBackgroundLowRegularitySolution (I := I) (M := M) g₀ g_bg K hT hT1
        u gforce Rcap Ctop₂ Kr2 Kr1 Kcap := by
  obtain ⟨Ctop₂, Kr2, Kr1, Kcap, hrung, hA, hB⟩ := hgate.2.2.1
  exact ⟨Ctop₂, Kr2, Kr1, Kcap, hsolve, hrung,
    A, B, hgate, hA, hB, hbudget⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.adaptedBackground_of_given then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.adaptedBackground_of_given"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.adaptedBackground_of_given ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.adaptedBackground_of_given

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
