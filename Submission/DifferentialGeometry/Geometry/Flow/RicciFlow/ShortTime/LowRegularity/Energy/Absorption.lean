import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Energy.H5
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Energy.RemainderLadder

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.Connection
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral hiding TensorEigenIdx
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.DeTurck
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization

theorem energyLadder_absorption_coefficient_le {Ctop Kr2 Kr1 Kcap A B δ R : ℝ}
    (hA : Ctop * Kcap ≤ A) (hB : Kr2 + Kr1 ≤ B)
    (hδ0 : 0 ≤ δ) (hR : 0 ≤ R) :
    Ctop * (Kcap * (δ / (1 - δ) ^ 2)) + Kr2 * R + Kr1 * R ≤
      A * (δ / (1 - δ) ^ 2) + B * R := by
  have hd : 0 ≤ δ / (1 - δ) ^ 2 := div_nonneg hδ0 (sq_nonneg _)
  calc
    Ctop * (Kcap * (δ / (1 - δ) ^ 2)) + Kr2 * R + Kr1 * R =
        (Ctop * Kcap) * (δ / (1 - δ) ^ 2) + (Kr2 + Kr1) * R := by
          ring
    _ ≤ A * (δ / (1 - δ) ^ 2) + B * R :=
      add_le_add (mul_le_mul_of_nonneg_right hA hd)
        (mul_le_mul_of_nonneg_right hB hR)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.energyLadder_absorption_coefficient_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.energyLadder_absorption_coefficient_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.energyLadder_absorption_coefficient_le ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.energyLadder_absorption_coefficient_le

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

def HasEnergyLadderAbsorptionConstants (g : SmoothRiemannianMetric I M) (A B : ℝ) : Prop :=
  0 ≤ A ∧ 0 ≤ B ∧
    (∃ C2 Kr23 Kr13 K2 : ℝ,
      HasGalerkinEnergyThreeBound (I := I) (M := M) g C2 Kr23 Kr13 K2 ∧
        C2 * K2 ≤ A ∧ Kr23 + Kr13 ≤ B) ∧
    (∃ C3 Kr24 Kr14 K3 : ℝ,
      HasGalerkinEnergyFourBound (I := I) (M := M) g C3 Kr24 Kr14 K3 ∧
        C3 * K3 ≤ A ∧ Kr24 + Kr14 ≤ B) ∧
    (∃ C4 Kr25 Kr15 K4 : ℝ,
      HasGalerkinEnergyFiveBound (I := I) (M := M) g C4 Kr25 Kr15 K4 ∧
        C4 * K4 ≤ A ∧ Kr25 + Kr15 ≤ B) ∧
    ∃ κ : ℝ, HasDeTurckRemainderAllOrderLadderBound (I := I) (M := M) g κ ∧ κ ≤ A

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.HasEnergyLadderAbsorptionConstants then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.HasEnergyLadderAbsorptionConstants"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.HasEnergyLadderAbsorptionConstants ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.HasEnergyLadderAbsorptionConstants

theorem exists_energy_ladder_absorption_constants (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ A B : ℝ, HasEnergyLadderAbsorptionConstants (I := I) (M := M) g A B := by
  obtain ⟨C2, Kr23, Kr13, K2, h2⟩ :=
    exists_galerkin_energy_three_bound_parameters (I := I) (M := M) hDim g
  obtain ⟨C3, Kr24, Kr14, K3, h3⟩ :=
    exists_galerkin_energy_four_bound_parameters (I := I) (M := M) hDim g
  obtain ⟨C4, Kr25, Kr15, K4, h4⟩ :=
    exists_galerkin_energy_five_bound_parameters (I := I) (M := M) hDim g
  obtain ⟨κ, hκ⟩ := exists_deTurck_remainder_all_order_ladder_bound_parameters (I := I) (M := M) hDim g
  let A : ℝ := C2 * K2 + C3 * K3 + C4 * K4 + κ
  let B : ℝ := (Kr23 + Kr13) + (Kr24 + Kr14) + (Kr25 + Kr15)
  have hC2K2 : 0 ≤ C2 * K2 := mul_nonneg h2.1 h2.2.2.2.1
  have hC3K3 : 0 ≤ C3 * K3 := mul_nonneg h3.1 h3.2.2.2.1
  have hC4K4 : 0 ≤ C4 * K4 := mul_nonneg h4.1 h4.2.2.2.1
  have hB3 : 0 ≤ Kr23 + Kr13 := add_nonneg h2.2.1 h2.2.2.1
  have hB4 : 0 ≤ Kr24 + Kr14 := add_nonneg h3.2.1 h3.2.2.1
  have hB5 : 0 ≤ Kr25 + Kr15 := add_nonneg h4.2.1 h4.2.2.1
  have hκ0 : 0 ≤ κ := hκ.1
  have hAnn : 0 ≤ A := by
    dsimp only [A]
    exact add_nonneg (add_nonneg (add_nonneg hC2K2 hC3K3) hC4K4) hκ0
  have hBnn : 0 ≤ B := by
    dsimp only [B]
    exact add_nonneg (add_nonneg hB3 hB4) hB5
  have hA2le : C2 * K2 ≤ A := by dsimp only [A]; linarith
  have hA3le : C3 * K3 ≤ A := by dsimp only [A]; linarith
  have hA4le : C4 * K4 ≤ A := by dsimp only [A]; linarith
  have hκle : κ ≤ A := by dsimp only [A]; linarith
  have hB3le : Kr23 + Kr13 ≤ B := by dsimp only [B]; linarith
  have hB4le : Kr24 + Kr14 ≤ B := by dsimp only [B]; linarith
  have hB5le : Kr25 + Kr15 ≤ B := by dsimp only [B]; linarith
  exact ⟨A, B, hAnn, hBnn,
    ⟨C2, Kr23, Kr13, K2, h2, hA2le, hB3le⟩,
    ⟨C3, Kr24, Kr14, K3, h3, hA3le, hB4le⟩,
    ⟨C4, Kr25, Kr15, K4, h4, hA4le, hB5le⟩,
    ⟨κ, hκ, hκle⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_energy_ladder_absorption_constants then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_energy_ladder_absorption_constants"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_energy_ladder_absorption_constants ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_energy_ladder_absorption_constants

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
