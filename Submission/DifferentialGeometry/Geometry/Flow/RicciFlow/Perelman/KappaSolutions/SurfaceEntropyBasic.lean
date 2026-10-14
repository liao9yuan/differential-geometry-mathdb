import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CurvatureNormalization
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceEntropyMinimum

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

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


def surfaceArea (g : SmoothRiemannianMetric I M) : ℝ :=
  (riemannianVolumeMeasure (I := I) (M := M) g).real Set.univ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceArea then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceArea"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceArea ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceArea


def totalScalarCurvature (g : SmoothRiemannianMetric I M) : ℝ :=
  ∫ x, metricScalarAt (I := I) g x ∂(riemannianVolumeMeasure (I := I) (M := M) g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.totalScalarCurvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.totalScalarCurvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.totalScalarCurvature ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.totalScalarCurvature


def meanScalarCurvature (g : SmoothRiemannianMetric I M) : ℝ :=
  totalScalarCurvature g / surfaceArea g

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.meanScalarCurvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.meanScalarCurvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.meanScalarCurvature ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.meanScalarCurvature


def surfaceEntropy (g : SmoothRiemannianMetric I M) : ℝ :=
  ∫ x, metricScalarAt (I := I) g x *
    Real.log (metricScalarAt (I := I) g x * surfaceArea g)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy

omit [T2Space M] [CompactSpace M] in
theorem metricScalarAt_scaleMetric
    (g : SmoothRiemannianMetric I M) (c : ℝ) (hc : 0 < c) (x : M) :
    metricScalarAt (I := I) (scaleMetric c hc g) x = c⁻¹ * metricScalarAt (I := I) g x := by
  let S : SolutionOn (I := I) (M := M) ancientTimeInterval :=
    ⟨⟨fun _ => g⟩⟩
  have h := congrFun (congrFun (parabolicSolution_scalar (I := I) S 0 c hc
    (by change (0 : ℝ) ≤ 0; exact le_rfl)) 0) x
  change metricScalarAt (I := I) (scaleMetric c hc g) x =
    c⁻¹ * metricScalarAt (I := I) g x at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricScalarAt_scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricScalarAt_scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricScalarAt_scaleMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricScalarAt_scaleMetric

omit [CompleteSpace E] in
theorem surfaceVolume_scaleMetric
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 2)
    (c : ℝ) (hc : 0 < c) :
    riemannianVolumeMeasure (I := I) (M := M) (scaleMetric c hc g) =
      ENNReal.ofReal c • riemannianVolumeMeasure (I := I) (M := M) g := by
  have h := volume_scaleMetric (I := I) (M := M) c hc g
  rw [hdim, ← ENNReal.ofReal_pow (Real.sqrt_nonneg c), Real.sq_sqrt hc.le] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceVolume_scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceVolume_scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceVolume_scaleMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceVolume_scaleMetric

omit [CompleteSpace E] in
theorem surfaceArea_scaleMetric
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 2)
    (c : ℝ) (hc : 0 < c) :
    surfaceArea (scaleMetric c hc g) = c * surfaceArea g := by
  unfold surfaceArea
  rw [surfaceVolume_scaleMetric g hdim c hc, _root_.MeasureTheory.measureReal_ennreal_smul_apply,
    ENNReal.toReal_ofReal hc.le]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceArea_scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceArea_scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceArea_scaleMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceArea_scaleMetric


theorem totalScalarCurvature_scaleMetric
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 2)
    (c : ℝ) (hc : 0 < c) :
    totalScalarCurvature (scaleMetric c hc g) = totalScalarCurvature g := by
  unfold totalScalarCurvature
  simp_rw [metricScalarAt_scaleMetric]
  rw [surfaceVolume_scaleMetric g hdim c hc, _root_.MeasureTheory.integral_smul_measure,
    ENNReal.toReal_ofReal hc.le, smul_eq_mul, _root_.MeasureTheory.integral_const_mul,
    ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.totalScalarCurvature_scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.totalScalarCurvature_scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.totalScalarCurvature_scaleMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.totalScalarCurvature_scaleMetric


theorem surfaceEntropy_scaleMetric
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 2)
    (c : ℝ) (hc : 0 < c) :
    surfaceEntropy (scaleMetric c hc g) = surfaceEntropy g := by
  have hproduct (x : M) :
      metricScalarAt (I := I) (scaleMetric c hc g) x * surfaceArea (scaleMetric c hc g) =
        metricScalarAt (I := I) g x * surfaceArea g := by
    rw [metricScalarAt_scaleMetric, surfaceArea_scaleMetric g hdim c hc]
    field_simp [hc.ne']
  unfold surfaceEntropy
  simp_rw [hproduct, metricScalarAt_scaleMetric]
  rw [surfaceVolume_scaleMetric g hdim c hc, _root_.MeasureTheory.integral_smul_measure,
    ENNReal.toReal_ofReal hc.le, smul_eq_mul]
  simp_rw [mul_assoc]
  rw [_root_.MeasureTheory.integral_const_mul, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_scaleMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_scaleMetric


theorem surfaceEntropy_lower_and_eq_iff_constant [Nonempty M]
    (g : SmoothRiemannianMetric I M)
    (hpositive : ∀ x : M, 0 < metricScalarAt (I := I) g x) :
    totalScalarCurvature g * Real.log (totalScalarCurvature g) ≤ surfaceEntropy g ∧
      (surfaceEntropy g = totalScalarCurvature g * Real.log (totalScalarCurvature g) ↔
        ∃ c : ℝ, ∀ x : M, metricScalarAt (I := I) g x = c) :=
  surfaceEntropy_minimum g hpositive

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_lower_and_eq_iff_constant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_lower_and_eq_iff_constant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_lower_and_eq_iff_constant ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_lower_and_eq_iff_constant

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
