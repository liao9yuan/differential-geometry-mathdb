import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedVolumeNormalization
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.W.Scaling

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Entropy
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Integral.Measure
open scoped _root_.ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] {D : RealTimeInterval}
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instBorelSpace_differentialGeometry target :: scope.openDecls } }

theorem intrinsicReducedVolume_eq_normalizedShrinkerMass
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (p : M) {tau : ℝ} (htau : 0 < tau) :
    intrinsicReducedVolume S T p tau =
      normalizedShrinkerMass (scaleMetric tau⁻¹ (inv_pos.mpr htau) (S.base.metric (T - tau)))
        (fun q => redLength S T p q tau) := by
  rw [normalizedShrinkerMass_scaleMetric_inv_eq_lintegral_perelmanDensity _ htau]
  apply _root_.MeasureTheory.lintegral_congr
  intro q
  apply congrArg ENNReal.ofReal
  rw [perelmanDensity, ← Real.exp_log (prefactor_pos (Module.finrank ℝ E) htau),
    log_prefactor (Module.finrank ℝ E) htau, ← Real.exp_add,
    Real.log_mul (show 4 * Real.pi ≠ 0 by positivity) htau.ne']
  congr 1
  dsimp only [redLength]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.intrinsicReducedVolume_eq_normalizedShrinkerMass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.intrinsicReducedVolume_eq_normalizedShrinkerMass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.intrinsicReducedVolume_eq_normalizedShrinkerMass ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.intrinsicReducedVolume_eq_normalizedShrinkerMass

theorem intrinsicReducedVolume_eq_lintegral_perelmanDensity_scaled
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (p : M)
    {c tau : ℝ} (hc : 0 < c) (htau : 0 < tau) :
    intrinsicReducedVolume S T p (c * tau) =
      ∫⁻ x, ENNReal.ofReal (perelmanDensity (Module.finrank ℝ E) tau
        (fun y => redLength S T p y (c * tau)) x)
        ∂riemannianVolumeMeasure (I := I) (M := M)
          (scaleMetric c⁻¹ (inv_pos.mpr hc) (S.base.metric (T - c * tau))) := by
  let g := scaleMetric (c * tau)⁻¹ (inv_pos.mpr (mul_pos hc htau))
    (S.base.metric (T - c * tau))
  have hg : scaleMetric c⁻¹ (inv_pos.mpr hc) (S.base.metric (T - c * tau)) =
      scaleMetric tau htau g := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    simp only [g, scaleMetric_inner]
    field_simp
  rw [intrinsicReducedVolume_eq_normalizedShrinkerMass S T p (mul_pos hc htau),
    normalizedShrinkerMass_eq_lintegral_perelmanDensity_one, hg]
  have h := setLIntegral_perelmanDensity_scaleMetric g htau zero_lt_one
    (fun y => redLength S T p y (c * tau)) Set.univ
  simpa only [mul_one, _root_.MeasureTheory.setLIntegral_univ] using h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.intrinsicReducedVolume_eq_lintegral_perelmanDensity_scaled then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.intrinsicReducedVolume_eq_lintegral_perelmanDensity_scaled"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.intrinsicReducedVolume_eq_lintegral_perelmanDensity_scaled ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.intrinsicReducedVolume_eq_lintegral_perelmanDensity_scaled

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
