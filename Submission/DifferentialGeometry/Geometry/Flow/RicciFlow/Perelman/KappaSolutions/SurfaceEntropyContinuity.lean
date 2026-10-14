import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceEntropyBasic
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Family.ParametricContinuity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M]

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
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instIsManifoldRealOfNatWithTopENat_differentialGeometry : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instIsManifoldRealOfNatWithTopENat_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instIsManifoldRealOfNatWithTopENat_differentialGeometry target :: scope.openDecls } }

omit [CompleteSpace E] in
theorem surfaceArea_pos [Nonempty M] (g : SmoothRiemannianMetric I M) :
    0 < surfaceArea g := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let _ : _root_.MeasureTheory.IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  let _ : μ.IsOpenPosMeasure :=
    riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := M) g
  exact _root_.MeasureTheory.measureReal_univ_pos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceArea_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceArea_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceArea_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceArea_pos

variable {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]

omit [CompleteSpace E] in
theorem surfaceArea_continuousOn
    {g : P → SmoothRiemannianMetric I M} {K : Set P} (hK : IsCompact K)
    (hg : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : P × M => chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (K ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ContinuousOn (fun p => surfaceArea (g p)) K := by
  have hi := integral_family_cont_param (I := I) (M := M)
    (g := g) (f := fun _ _ => (1 : ℝ)) hK hg continuousOn_const
  simpa only [riemannianMeasureFamily_def, _root_.MeasureTheory.integral_const, smul_eq_mul,
    mul_one, surfaceArea] using hi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceArea_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceArea_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceArea_continuousOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceArea_continuousOn

theorem totalScalarCurvature_continuousOn
    {g : P → SmoothRiemannianMetric I M} {K : Set P} (hK : IsCompact K)
    (hg : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : P × M => chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (K ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet))
    (hR : ContinuousOn (fun p : P × M => metricScalarAt (I := I) (g p.1) p.2)
      (K ×ˢ Set.univ)) :
    ContinuousOn (fun p => totalScalarCurvature (g p)) K := by
  simpa only [totalScalarCurvature, riemannianMeasureFamily_def] using
    integral_family_cont_param (I := I) (M := M)
      (g := g) (f := fun p x => metricScalarAt (I := I) (g p) x) hK hg hR

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.totalScalarCurvature_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.totalScalarCurvature_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.totalScalarCurvature_continuousOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.totalScalarCurvature_continuousOn

theorem surfaceEntropy_continuousOn [Nonempty M]
    {g : P → SmoothRiemannianMetric I M} {K : Set P} (hK : IsCompact K)
    (hg : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : P × M => chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (K ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet))
    (hR : ContinuousOn (fun p : P × M => metricScalarAt (I := I) (g p.1) p.2)
      (K ×ˢ Set.univ)) :
    ContinuousOn (fun p => surfaceEntropy (g p)) K := by
  have hA := surfaceArea_continuousOn hK hg
  have hAjoint : ContinuousOn (fun p : P × M => surfaceArea (g p.1))
      (K ×ˢ Set.univ) :=
    hA.comp continuous_fst.continuousOn (fun _ hp => hp.1)
  have hAinv : ContinuousOn (fun p : P × M => (surfaceArea (g p.1))⁻¹)
      (K ×ˢ Set.univ) :=
    hAjoint.inv₀ (fun p _ => (surfaceArea_pos (g p.1)).ne')
  have hmulLog : ContinuousOn
      (fun p : P × M =>
        (surfaceArea (g p.1) * metricScalarAt (I := I) (g p.1) p.2) *
          Real.log (surfaceArea (g p.1) * metricScalarAt (I := I) (g p.1) p.2))
      (K ×ˢ Set.univ) :=
    Real.continuous_mul_log.comp_continuousOn (hAjoint.mul hR)
  have hintegrand : ContinuousOn
      (fun p : P × M => metricScalarAt (I := I) (g p.1) p.2 *
        Real.log (metricScalarAt (I := I) (g p.1) p.2 * surfaceArea (g p.1)))
      (K ×ˢ Set.univ) := by
    apply (hAinv.mul hmulLog).congr
    intro p _
    let A := surfaceArea (g p.1)
    let R := metricScalarAt (I := I) (g p.1) p.2
    have hAne : A ≠ 0 := (surfaceArea_pos (g p.1)).ne'
    change R * Real.log (R * A) = A⁻¹ * ((A * R) * Real.log (A * R))
    rw [mul_comm R A]
    calc
      R * Real.log (A * R) = (A⁻¹ * A) * (R * Real.log (A * R)) := by
        rw [inv_mul_cancel₀ hAne, one_mul]
      _ = A⁻¹ * ((A * R) * Real.log (A * R)) := by ring
  simpa only [surfaceEntropy, riemannianMeasureFamily_def] using
    integral_family_cont_param (I := I) (M := M)
      (g := g) (f := fun p x => metricScalarAt (I := I) (g p) x *
        Real.log (metricScalarAt (I := I) (g p) x * surfaceArea (g p))) hK hg hintegrand

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_continuousOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_continuousOn

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
