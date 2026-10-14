import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWitnessVolume
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.E3 target :: scope.openDecls } }
private abbrev Cap := {x : E3 // ‖x‖ ≤ transitionEnd}

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.Cap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.Cap target :: scope.openDecls } }
private instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instCompactSpaceCap : CompactSpace Cap :=
  (DifferentialGeometry.Topology.Manifold.closedBallUnitHomeomorph transitionEnd_pos).symm.compactSpace

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instCompactSpaceCap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instCompactSpaceCap target :: scope.openDecls } }
private instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instMeasurableSpaceE3 : MeasurableSpace E3 := borel E3

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instMeasurableSpaceE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instMeasurableSpaceE3 target :: scope.openDecls } }
private instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instBorelSpaceE3 : BorelSpace E3 := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instBorelSpaceE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instBorelSpaceE3 target :: scope.openDecls } }

private theorem cap_volume_ne_top :
    riemannianVolumeMeasure (𝓡 3) E3 metric {x | ‖x‖ ≤ transitionEnd} ≠ (∞ : ℝ≥0∞) := by
  let : _root_.MeasureTheory.IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (𝓡 3) E3 metric) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts metric
  exact (isCompact_iff_compactSpace.mpr (inferInstance : CompactSpace Cap)).measure_lt_top.ne

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.cap_volume_ne_top
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.cap_volume_ne_top target :: scope.openDecls } }

theorem cap_volume_margin_of_precision_le (δ Q : ℝ) (hδ : 0 < δ) (hQ : 0 < Q)
    (hsmall : δ ≤ Real.pi /
      (8 * (riemannianVolumeMeasure (𝓡 3) E3 metric {x | ‖x‖ ≤ transitionEnd}).toReal + 1)) :
    ENNReal.ofReal (8 * Q ^ (-3 / 2 : ℝ)) *
        riemannianVolumeMeasure (𝓡 3) E3 metric {x | ‖x‖ ≤ transitionEnd} +
      ENNReal.ofReal (Q ^ (-3 / 2 : ℝ)) ≤
      ENNReal.ofReal (2 * Real.pi / δ) * ENNReal.ofReal (Q ^ (-3 / 2 : ℝ)) := by
  let V := riemannianVolumeMeasure (𝓡 3) E3 metric {x | ‖x‖ ≤ transitionEnd}
  have hV : ENNReal.ofReal V.toReal = V := ENNReal.ofReal_toReal cap_volume_ne_top
  have hp : 0 < 8 * V.toReal + 1 := by positivity
  have hbound : 8 * V.toReal + 1 ≤ 2 * Real.pi / δ := by
    have hs := (le_div_iff₀ hp).mp hsmall
    exact (le_div_iff₀ hδ).mpr (by nlinarith [Real.pi_pos])
  have hqn : 0 ≤ Q ^ (-3 / 2 : ℝ) := Real.rpow_nonneg hQ.le _
  change ENNReal.ofReal (8 * Q ^ (-3 / 2 : ℝ)) * V + ENNReal.ofReal (Q ^ (-3 / 2 : ℝ)) ≤ _
  rw [← hV, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) hqn, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc
    8 * Q ^ (-3 / 2 : ℝ) * V.toReal + Q ^ (-3 / 2 : ℝ) =
      (8 * V.toReal + 1) * Q ^ (-3 / 2 : ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hbound hqn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.cap_volume_margin_of_precision_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.cap_volume_margin_of_precision_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.cap_volume_margin_of_precision_le ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.cap_volume_margin_of_precision_le

end DifferentialGeometry.PDE.RicciFlow.StandardCap
