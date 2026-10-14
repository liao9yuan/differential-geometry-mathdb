import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ReducedVolumeComplete
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

private theorem setVolume_density_factor (n : ℕ) (tau L : ℝ) (htau : 0 < tau) :
    Real.exp (-L - ((n : ℝ) / 2) * Real.log tau -
        ((n : ℝ) / 2) * Real.log (4 * Real.pi)) =
      (4 * Real.pi * tau) ^ (-(n : ℝ) / 2) * Real.exp (-L) := by
  have hpi : 0 < 4 * Real.pi := by positivity
  rw [Real.rpow_def_of_pos (mul_pos hpi htau), ← Real.exp_add,
    Real.log_mul hpi.ne' htau.ne']
  congr 1
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.setVolume_density_factor
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.setVolume_density_factor target :: scope.openDecls } }

private theorem setVolume_density_factor_pos (n : ℕ) (tau L : ℝ) (htau : 0 < tau) :
    0 < (4 * Real.pi * tau) ^ (-(n : ℝ) / 2) * Real.exp (-L) :=
  mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.exp_pos _)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.setVolume_density_factor_pos
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.setVolume_density_factor_pos target :: scope.openDecls } }

section General

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval}

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry target :: scope.openDecls } }

theorem redVolume_set_lower
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (x : M)
    (tau L : ℝ) (htau : 0 < tau) {A : Set M} (hA : MeasurableSet A)
    (hL : ∀ y ∈ A, redLength S T x y tau ≤ L) :
    riemannianVolumeMeasure (I := I) (M := M) (S.base.metric (T - tau)) A *
        ENNReal.ofReal ((4 * Real.pi * tau) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
          Real.exp (-L)) ≤
      DifferentialGeometry.PDE.RicciFlow.redVolume S T x tau := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) (S.base.metric (T - tau))
  let c := (4 * Real.pi * tau) ^ (-(Module.finrank ℝ E : ℝ) / 2) * Real.exp (-L)
  have hc : ∀ y ∈ A, ENNReal.ofReal c ≤ ENNReal.ofReal (redDensity S T x y tau) := by
    intro y hy
    apply ENNReal.ofReal_le_ofReal
    rw [show c = Real.exp (-L - ((Module.finrank ℝ E : ℝ) / 2) * Real.log tau -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)) from
      (setVolume_density_factor (Module.finrank ℝ E) tau L htau).symm]
    unfold redDensity
    apply Real.exp_le_exp.mpr
    linarith [hL y hy]
  calc
    μ A * ENNReal.ofReal c = ENNReal.ofReal c * μ A := mul_comm _ _
    _ = ∫⁻ _y in A, ENNReal.ofReal c ∂μ := by rw [_root_.MeasureTheory.setLIntegral_const]
    _ ≤ ∫⁻ y in A, ENNReal.ofReal (redDensity S T x y tau) ∂μ :=
      _root_.MeasureTheory.setLIntegral_mono' hA hc
    _ ≤ ∫⁻ y, ENNReal.ofReal (redDensity S T x y tau) ∂μ := by
      simpa using _root_.MeasureTheory.lintegral_mono_set (_root_.Set.subset_univ A)
    _ = DifferentialGeometry.PDE.RicciFlow.redVolume S T x tau := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.redVolume_set_lower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.redVolume_set_lower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.redVolume_set_lower ``Submission.DifferentialGeometry.PDE.RicciFlow.redVolume_set_lower

theorem redVolume_toReal_set_lower
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (x : M)
    (tau L : ℝ) (htau : 0 < tau) {A : Set M} (hA : MeasurableSet A)
    (hL : ∀ y ∈ A, redLength S T x y tau ≤ L)
    (hfinite : DifferentialGeometry.PDE.RicciFlow.redVolume S T x tau ≠ ⊤) :
    riemannianVolumeMeasure (I := I) (M := M) (S.base.metric (T - tau)) A ≠ ⊤ ∧
      (riemannianVolumeMeasure (I := I) (M := M) (S.base.metric (T - tau)) A).toReal *
          ((4 * Real.pi * tau) ^ (-(Module.finrank ℝ E : ℝ) / 2) * Real.exp (-L)) ≤
        (DifferentialGeometry.PDE.RicciFlow.redVolume S T x tau).toReal := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) (S.base.metric (T - tau))
  let c := (4 * Real.pi * tau) ^ (-(Module.finrank ℝ E : ℝ) / 2) * Real.exp (-L)
  have hc : 0 < c := setVolume_density_factor_pos (Module.finrank ℝ E) tau L htau
  have hlow : μ A * ENNReal.ofReal c ≤ DifferentialGeometry.PDE.RicciFlow.redVolume S T x tau :=
    redVolume_set_lower S T x tau L htau hA hL
  have hprod : μ A * ENNReal.ofReal c ≠ ⊤ := ne_top_of_le_ne_top hfinite hlow
  have hAfinite : μ A ≠ ⊤ := by
    intro htop
    apply hprod
    rw [htop, ENNReal.top_mul (ne_of_gt (ENNReal.ofReal_pos.mpr hc))]
  have hreal := ENNReal.toReal_mono hfinite hlow
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le] at hreal
  exact ⟨hAfinite, hreal⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.redVolume_toReal_set_lower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.redVolume_toReal_set_lower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.redVolume_toReal_set_lower ``Submission.DifferentialGeometry.PDE.RicciFlow.redVolume_toReal_set_lower

end General

end DifferentialGeometry.PDE.RicciFlow

end
