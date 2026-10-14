import Submission.DifferentialGeometry.Analysis.Integration.Measure.PullbackCross

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory
open scoped _root_.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
  [IsManifold I ∞ N]

private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry_2 : MeasurableSpace N := borel N

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry_2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry_2 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry_2 : BorelSpace N := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry_2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry_2 target :: scope.openDecls } }

theorem riemannianVolumeMeasure_pullback
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    [T2Space N] [SigmaCompactSpace N]
    (g : SmoothRiemannianMetric I N) (Phi : M ≃ₘ⟮I, I⟯ N) :
    riemannianVolumeMeasure (I := I) (M := M)
        (Diffeomorph.pullbackMetric g Phi) =
      Measure.map (Phi.symm : N → M)
        (riemannianVolumeMeasure (I := I) (M := N) g) := by
  simpa only [Diffeomorph.pullbackMetricCross_eq_pullbackMetric] using
    riemannianVolumeMeasure_pullback_cross g Phi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_pullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_pullback ``Submission.DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_pullback

omit [FiniteDimensional Real E] [IsManifold I ∞ M] [IsManifold I ∞ N] in
private theorem map_symm_withDensity
    (mu : _root_.MeasureTheory.Measure N) (Phi : M ≃ₘ⟮I, I⟯ N)
    (rho : M → ENNReal) (hrho : Measurable rho) :
    (Measure.map (Phi.symm : N → M) mu).withDensity rho =
      Measure.map (Phi.symm : N → M)
        (mu.withDensity (fun y => rho (Phi.symm y))) := by
  ext A hA
  rw [MeasureTheory.withDensity_apply _ hA]
  rw [MeasureTheory.setLIntegral_map hA hrho Phi.symm.continuous.measurable]
  rw [Measure.map_apply Phi.symm.continuous.measurable hA]
  have hpre : MeasurableSet ((Phi.symm : N → M) ⁻¹' A) :=
    Phi.symm.continuous.measurable hA
  rw [MeasureTheory.withDensity_apply _ hpre]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.map_symm_withDensity
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.map_symm_withDensity target :: scope.openDecls } }

theorem riemannianVolumeMeasure_pullback_withDensity
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    [T2Space N] [SigmaCompactSpace N]
    (g : SmoothRiemannianMetric I N) (Phi : M ≃ₘ⟮I, I⟯ N)
    (rho : M → ENNReal) (hrho : Measurable rho) :
    (riemannianVolumeMeasure (I := I) (M := M)
        (Diffeomorph.pullbackMetric g Phi)).withDensity rho =
      Measure.map (Phi.symm : N → M)
        ((riemannianVolumeMeasure (I := I) (M := N) g).withDensity
          (fun y => rho (Phi.symm y))) := by
  rw [riemannianVolumeMeasure_pullback (I := I) g Phi]
  exact map_symm_withDensity (I := I)
    (riemannianVolumeMeasure (I := I) (M := N) g) Phi rho hrho

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_pullback_withDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_pullback_withDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_pullback_withDensity ``Submission.DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_pullback_withDensity

end DifferentialGeometry.Integral.Measure
