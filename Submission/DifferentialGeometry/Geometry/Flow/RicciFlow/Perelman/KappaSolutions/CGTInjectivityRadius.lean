import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalCGTInjectivity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

private local instance selectedInjMeasurableE : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.selectedInjMeasurableE
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.selectedInjMeasurableE target :: scope.openDecls } }
private local instance selectedInjBorelE : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.selectedInjBorelE
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.selectedInjBorelE target :: scope.openDecls } }

def selectedCGTDenominator (E : Type uE) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (R : ℝ) : ℝ :=
  1 + ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere
      Set.univ).toReal * hyperbolicRadialVolume 0 (Module.finrank ℝ E - 1) (R / 8) +
    ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).toSphere Set.univ).toReal *
      hyperbolicRadialVolume 0 (Module.finrank ℝ E - 1) (R / 4)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.selectedCGTDenominator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.selectedCGTDenominator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.selectedCGTDenominator ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.selectedCGTDenominator


def selectedCGTInjRadius (E : Type uE) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (kappa R : ℝ) : ℝ :=
  (R / 16) * (kappa * (R / 8) ^ Module.finrank ℝ E) / selectedCGTDenominator E R

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.selectedCGTInjRadius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.selectedCGTInjRadius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.selectedCGTInjRadius ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.selectedCGTInjRadius

theorem selectedCGTDenominator_pos {R : ℝ} (hR : 0 < R) :
    0 < selectedCGTDenominator E R := by
  have hsmall : 0 ≤ hyperbolicRadialVolume 0 (Module.finrank ℝ E - 1) (R / 8) :=
    (hyperbolicRadialVolume_pos (by norm_num : (0 : ℝ) ≤ 0) (by positivity)).le
  have hlarge : 0 ≤ hyperbolicRadialVolume 0 (Module.finrank ℝ E - 1) (R / 4) :=
    (hyperbolicRadialVolume_pos (by norm_num : (0 : ℝ) ≤ 0) (by positivity)).le
  unfold selectedCGTDenominator
  positivity

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.selectedCGTDenominator_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.selectedCGTDenominator_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.selectedCGTDenominator_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.selectedCGTDenominator_pos

theorem selectedCGTInjRadius_pos {kappa R : ℝ} (hκ : 0 < kappa) (hR : 0 < R) :
    0 < selectedCGTInjRadius E kappa R := by
  unfold selectedCGTInjRadius
  exact div_pos (mul_pos (by positivity) (mul_pos hκ (pow_pos (by positivity) _)))
    (selectedCGTDenominator_pos (E := E) hR)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.selectedCGTInjRadius_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.selectedCGTInjRadius_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.selectedCGTInjRadius_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.selectedCGTInjRadius_pos

variable [NeZero (Module.finrank ℝ E)]

theorem selectedCGTInjRadius_le_quotient {kappa R : ℝ}
    (hκ : 0 ≤ kappa) (hR : 0 < R) :
    ENNReal.ofReal (selectedCGTInjRadius E kappa R) ≤
      ENNReal.ofReal (R / 16) *
        (ENNReal.ofReal kappa * ENNReal.ofReal (R / 8) ^ Module.finrank ℝ E) /
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere
            Set.univ * ENNReal.ofReal (hyperbolicRadialVolume 0 (Module.finrank ℝ E - 1) (R / 8)) +
          (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).toSphere Set.univ *
            ENNReal.ofReal (hyperbolicRadialVolume 0 (Module.finrank ℝ E - 1) (R / 4))) := by
  let _ : Nontrivial E := Module.nontrivial_of_finrank_pos
    (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  have hfin : 0 < Module.finrank ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) := by
    simpa only [finrank_euclideanSpace, Fintype.card_fin] using
      Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))
  let _ : Nontrivial (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    Module.nontrivial_of_finrank_pos hfin
  let b : ℝ := ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (EuclideanSpace ℝ
    (Fin (Module.finrank ℝ E)))).toSphere Set.univ).toReal
  let p : ℝ := ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).toSphere Set.univ).toReal
  let m : ℝ := hyperbolicRadialVolume 0 (Module.finrank ℝ E - 1) (R / 8)
  let l : ℝ := hyperbolicRadialVolume 0 (Module.finrank ℝ E - 1) (R / 4)
  have hb : 0 ≤ b := ENNReal.toReal_nonneg
  have hp : 0 ≤ p := ENNReal.toReal_nonneg
  have hm : 0 ≤ m := (hyperbolicRadialVolume_pos (by norm_num : (0 : ℝ) ≤ 0) (by positivity)).le
  have hl : 0 ≤ l := (hyperbolicRadialVolume_pos (by norm_num : (0 : ℝ) ≤ 0) (by positivity)).le
  have hbeq : (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere
      Set.univ = ENNReal.ofReal b :=
    (ENNReal.ofReal_toReal (_root_.MeasureTheory.measure_lt_top _ _).ne).symm
  have hpeq : (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).toSphere Set.univ = ENNReal.ofReal p :=
    (ENNReal.ofReal_toReal (_root_.MeasureTheory.measure_lt_top _ _).ne).symm
  have hden :
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere Set.univ *
          ENNReal.ofReal m + (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).toSphere Set.univ * ENNReal.ofReal l ≤
        ENNReal.ofReal (selectedCGTDenominator E R) := by
    rw [hbeq, hpeq, ← ENNReal.ofReal_mul hb, ← ENNReal.ofReal_mul hp,
      ← ENNReal.ofReal_add (mul_nonneg hb hm) (mul_nonneg hp hl)]
    apply ENNReal.ofReal_le_ofReal
    change b * m + p * l ≤ 1 + b * m + p * l
    linarith
  rw [selectedCGTInjRadius,
    ENNReal.ofReal_div_of_pos (selectedCGTDenominator_pos (E := E) hR),
    ENNReal.ofReal_mul (by positivity : 0 ≤ R / 16), ENNReal.ofReal_mul hκ,
    ENNReal.ofReal_pow (by positivity : 0 ≤ R / 8)]
  exact ENNReal.div_le_div le_rfl hden

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.selectedCGTInjRadius_le_quotient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.selectedCGTInjRadius_le_quotient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.selectedCGTInjRadius_le_quotient ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.selectedCGTInjRadius_le_quotient


end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
