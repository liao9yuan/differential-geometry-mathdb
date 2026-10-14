import Submission.DifferentialGeometry.Analysis.Integration.Measure.Family.VolumeVariation
import Submission.DifferentialGeometry.Geometry.Curvature.Sections.Trace
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

open _root_.Submission.DifferentialGeometry.Analysis
namespace DifferentialGeometry.PDE.RicciFlow
namespace Evolution
namespace Volume

open _root_.MeasureTheory
open _root_.Submission.DifferentialGeometry.Integral.Measure
open scoped _root_.BigOperators _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {A : Type*} [CommRing A] [Algebra Real A]

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

abbrev volumeTraceFrame :
    Fin (Module.finrank Real E) → (x : M) → TangentSpace I x :=
  fun i x => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x i x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.volumeTraceFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.volumeTraceFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.volumeTraceFrame ``Submission.DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.volumeTraceFrame

abbrev volumeTraceInvMetricComponents
    (g : DifferentialGeometry.SmoothRiemannianMetric I M) :
    M → Fin (Module.finrank Real E) → Fin (Module.finrank Real E) → Real :=
  fun x i j => ((DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g x x)⁻¹) i j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.volumeTraceInvMetricComponents then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.volumeTraceInvMetricComponents"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.volumeTraceInvMetricComponents ``Submission.DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.volumeTraceInvMetricComponents

abbrev scalarCurvatureFromRicciInVolumeFrame
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real)
    (Ric : DifferentialGeometry.PDE.RicciFlow.RicciTensorField (I := I) (M := M) Real) :
    Real → M → Real :=
  fun t =>
    DifferentialGeometry.Geometry.Curvature.scalarCurvatureFromRicciTraceInFrame (I := I) (Ric t)
      (volumeTraceInvMetricComponents (I := I) (M := M) (G.metric t))
      (volumeTraceFrame (I := I) (M := M))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.scalarCurvatureFromRicciInVolumeFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.scalarCurvatureFromRicciInVolumeFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.scalarCurvatureFromRicciInVolumeFrame ``Submission.DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.scalarCurvatureFromRicciInVolumeFrame

theorem scalarCurvatureFromRicciInVolumeFrame_realizes
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real)
    (Ric : DifferentialGeometry.PDE.RicciFlow.RicciTensorField (I := I) (M := M) Real)
      (t : Real) :
    DifferentialGeometry.Geometry.Curvature.scalarRealizesRicciTraceInFrame (I := I)
      (scalarCurvatureFromRicciInVolumeFrame (I := I) (M := M) G Ric t)
      (Ric t)
      (volumeTraceInvMetricComponents (I := I) (M := M) (G.metric t))
      (volumeTraceFrame (I := I) (M := M)) :=
  DifferentialGeometry.Geometry.Curvature.scalarCurvatureFromRicciTraceInFrame_realizes
    (I := I) (M := M) (Ric t)
    (volumeTraceInvMetricComponents (I := I) (M := M) (G.metric t))
    (volumeTraceFrame (I := I) (M := M))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.scalarCurvatureFromRicciInVolumeFrame_realizes then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.scalarCurvatureFromRicciInVolumeFrame_realizes"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.scalarCurvatureFromRicciInVolumeFrame_realizes ``Submission.DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.scalarCurvatureFromRicciInVolumeFrame_realizes

theorem traceTimeDerivMetricAt_eq_trace_metric_derivative
    (td : TimeDerivativeData Real A Real)
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real)
    {t : Real} {x : M}
    (hdt : ∀ F : Real → Real, td.dtApply F t = deriv F t) :
    traceTimeDerivMetricAt (I := I) G t x =
      Matrix.trace
        ((DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (G.metric t) x x)⁻¹ *
          Matrix.of fun i j =>
            DifferentialGeometry.Geometry.Curvature.metricTimeDerivative td G t x
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x i x)
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x j x)) := by
  rw [traceTimeDerivMetricAt_eq, traceTimeDerivMetric_eq]
  congr 2
  ext i j
  have h := hdt
    (fun s : Real =>
      (G.metric s).inner x
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x i x)
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x j x))
  simpa [metricFamilyForMeasure, DifferentialGeometry.Geometry.Curvature.metricTimeDerivative,
    DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply]
    using h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.traceTimeDerivMetricAt_eq_trace_metric_derivative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.traceTimeDerivMetricAt_eq_trace_metric_derivative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.traceTimeDerivMetricAt_eq_trace_metric_derivative ``Submission.DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.traceTimeDerivMetricAt_eq_trace_metric_derivative

private theorem chartGramMatrix_inv_symm
    (g : DifferentialGeometry.SmoothRiemannianMetric I M) (x : M)
    (i j : Fin (Module.finrank Real E)) :
    ((DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g x x)⁻¹) j i =
      ((DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g x x)⁻¹) i j := by
  have hHerm :
      ((DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g x x)⁻¹).IsHermitian :=
    (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_isHermitian (I := I) g x x).inv
  simpa [_root_.TrivialStar.star_trivial] using hHerm.apply i j

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.chartGramMatrix_inv_symm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.chartGramMatrix_inv_symm target :: scope.openDecls } }

theorem scalar_trace_eq_volume_trace_components
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (Ric : DifferentialGeometry.Geometry.Curvature.RawTwoTensorField (I := I) (M := M))
    (scalar : M → Real)
    (hScalar : DifferentialGeometry.Geometry.Curvature.scalarRealizesRicciTraceInFrame (I := I)
      scalar Ric
      (volumeTraceInvMetricComponents (I := I) (M := M) g)
      (volumeTraceFrame (I := I) (M := M))) (x : M) :
    scalar x =
      ∑ i : Fin (Module.finrank Real E),
        ∑ j : Fin (Module.finrank Real E),
          ((DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g x x)⁻¹) i j *
            Ric x
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x i x)
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x j x) := by
  simpa [volumeTraceInvMetricComponents, volumeTraceFrame] using
    DifferentialGeometry.Geometry.Curvature.scalar_eq_trace (I := I) scalar Ric
      (volumeTraceInvMetricComponents (I := I) (M := M) g)
      (volumeTraceFrame (I := I) (M := M)) hScalar x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.scalar_trace_eq_volume_trace_components then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.scalar_trace_eq_volume_trace_components"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.scalar_trace_eq_volume_trace_components ``Submission.DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.scalar_trace_eq_volume_trace_components

theorem traceTimeDerivMetricAt_eq_neg_two_scalar
    (td : TimeDerivativeData Real A Real)
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real)
    (Ric : DifferentialGeometry.PDE.RicciFlow.RicciTensorField (I := I) (M := M) Real)
    (scalar : Real → M → Real)
    (hdt : ∀ (F : Real → Real) (t : Real), td.dtApply F t = deriv F t)
    (hEq : DifferentialGeometry.PDE.RicciFlow.MetricVariationEquation (I := I) td G Ric)
    {t : Real} {x : M}
    (hScalar :
      scalar t x =
        ∑ i : Fin (Module.finrank Real E),
          ∑ j : Fin (Module.finrank Real E),
            ((DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (G.metric t) x x)⁻¹) i j *
              Ric t x
                (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x i x)
                (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x j x)) :
    traceTimeDerivMetricAt (I := I) G t x = (-2 : Real) * scalar t x := by
  classical
  let Gmat : Matrix (Fin (Module.finrank Real E)) (Fin (Module.finrank Real E)) Real :=
    DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (G.metric t) x x
  let dG : Matrix (Fin (Module.finrank Real E)) (Fin (Module.finrank Real E)) Real :=
    Matrix.of fun i j =>
      DifferentialGeometry.Geometry.Curvature.metricTimeDerivative td G t x
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x i x)
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x j x)
  have htrace :
      traceTimeDerivMetricAt (I := I) G t x =
        Matrix.trace (Gmat⁻¹ * dG) := by
    simpa [Gmat, dG] using
      traceTimeDerivMetricAt_eq_trace_metric_derivative
        (I := I) (M := M) td G (t := t) (x := x) (fun F => hdt F t)
  have hdG :
      dG =
        Matrix.of fun i j : Fin (Module.finrank Real E) =>
          (-2 : Real) *
            Ric t x
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x i x)
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x j x) := by
    ext i j
    simpa [dG] using (hEq t x
      (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x i x)
      (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x j x))
  have hInvSymm :
      ∀ i j : Fin (Module.finrank Real E), Gmat⁻¹ j i = Gmat⁻¹ i j := by
    intro i j
    simpa [Gmat] using
      chartGramMatrix_inv_symm (I := I) (M := M) (G.metric t) x i j
  rw [htrace, hdG]
  calc
    Matrix.trace
        (Gmat⁻¹ *
          Matrix.of fun i j : Fin (Module.finrank Real E) =>
            (-2 : Real) *
              Ric t x
                (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x i x)
                (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x j x))
        =
        Matrix.trace
          ((Matrix.of fun i j : Fin (Module.finrank Real E) =>
            (-2 : Real) *
              Ric t x
                (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x i x)
                (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x j x)) * Gmat⁻¹) := by
          rw [Matrix.trace_mul_comm]
    _ =
        ∑ i : Fin (Module.finrank Real E),
          ∑ j : Fin (Module.finrank Real E),
            ((-2 : Real) *
              Ric t x
                (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x i x)
                (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x j x)) * Gmat⁻¹ j i := by
          simp [Matrix.trace, Matrix.mul_apply]
    _ =
        (-2 : Real) *
          (∑ i : Fin (Module.finrank Real E),
            ∑ j : Fin (Module.finrank Real E),
              Gmat⁻¹ i j *
                Ric t x
                  (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x i x)
                  (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x j x)) := by
          simp_rw [hInvSymm]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro j hj
          ring
    _ = (-2 : Real) * scalar t x := by
          rw [hScalar]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.traceTimeDerivMetricAt_eq_neg_two_scalar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.traceTimeDerivMetricAt_eq_neg_two_scalar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.traceTimeDerivMetricAt_eq_neg_two_scalar ``Submission.DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.traceTimeDerivMetricAt_eq_neg_two_scalar

theorem traceTimeDerivMetricAt_eq_neg_two_scalar_of_scalarTrace
    (td : TimeDerivativeData Real A Real)
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real)
    (Ric : DifferentialGeometry.PDE.RicciFlow.RicciTensorField (I := I) (M := M) Real)
    (scalar : Real → M → Real)
    (hdt : ∀ (F : Real → Real) (t : Real), td.dtApply F t = deriv F t)
    (hEq : DifferentialGeometry.PDE.RicciFlow.MetricVariationEquation (I := I) td G Ric)
    {t : Real}
    (hScalar : DifferentialGeometry.Geometry.Curvature.scalarRealizesRicciTraceInFrame (I := I)
      (scalar t) (Ric t)
      (volumeTraceInvMetricComponents (I := I) (M := M) (G.metric t))
      (volumeTraceFrame (I := I) (M := M)))
    (x : M) :
    traceTimeDerivMetricAt (I := I) G t x = (-2 : Real) * scalar t x :=
  traceTimeDerivMetricAt_eq_neg_two_scalar
    (I := I) (M := M) td G Ric scalar hdt hEq (t := t) (x := x)
    (scalar_trace_eq_volume_trace_components
      (I := I) (M := M) (G.metric t) (Ric t) (scalar t) hScalar x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.traceTimeDerivMetricAt_eq_neg_two_scalar_of_scalarTrace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.traceTimeDerivMetricAt_eq_neg_two_scalar_of_scalarTrace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.traceTimeDerivMetricAt_eq_neg_two_scalar_of_scalarTrace ``Submission.DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.traceTimeDerivMetricAt_eq_neg_two_scalar_of_scalarTrace

theorem traceTimeDerivMetricAt_eq_neg_two_scalar_of_metricDeriv
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real)
    (Ric : DifferentialGeometry.PDE.RicciFlow.RicciTensorField (I := I) (M := M) Real)
    (scalar : Real → M → Real)
    {t : Real}
    (hEq : DifferentialGeometry.PDE.RicciFlow.MetricVariationEquationDerivAt (I := I) G Ric t)
    (hScalar : DifferentialGeometry.Geometry.Curvature.scalarRealizesRicciTraceInFrame (I := I)
      (scalar t) (Ric t)
      (volumeTraceInvMetricComponents (I := I) (M := M) (G.metric t))
      (volumeTraceFrame (I := I) (M := M)))
    (x : M) :
    traceTimeDerivMetricAt (I := I) G t x = (-2 : Real) * scalar t x := by
  classical
  let Gmat : Matrix (Fin (Module.finrank Real E)) (Fin (Module.finrank Real E)) Real :=
    DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (G.metric t) x x
  let dG : Matrix (Fin (Module.finrank Real E)) (Fin (Module.finrank Real E)) Real :=
    Matrix.of fun i j =>
      deriv (fun s : Real =>
        (G.metric s).inner x
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x i x)
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x j x)) t
  have htrace :
      traceTimeDerivMetricAt (I := I) G t x =
        Matrix.trace (Gmat⁻¹ * dG) := by
    simp [traceTimeDerivMetric_eq, metricFamilyForMeasure,
      DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply, Gmat, dG]
  have hdG :
      dG =
        Matrix.of fun i j : Fin (Module.finrank Real E) =>
          (-2 : Real) *
            Ric t x
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x i x)
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x j x) := by
    ext i j
    simpa [dG] using
      DifferentialGeometry.PDE.RicciFlow.metric_deriv_eq_neg_two_ricci_of_metricVariationEquationDerivAt
        (I := I) G Ric hEq x
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x i x)
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x j x)
  have hInvSymm :
      ∀ i j : Fin (Module.finrank Real E), Gmat⁻¹ j i = Gmat⁻¹ i j := by
    intro i j
    simpa [Gmat] using
      chartGramMatrix_inv_symm (I := I) (M := M) (G.metric t) x i j
  rw [htrace, hdG]
  calc
    Matrix.trace
        (Gmat⁻¹ *
          Matrix.of fun i j : Fin (Module.finrank Real E) =>
            (-2 : Real) *
              Ric t x
                (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x i x)
                (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x j x))
        =
        Matrix.trace
          ((Matrix.of fun i j : Fin (Module.finrank Real E) =>
            (-2 : Real) *
              Ric t x
                (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x i x)
                (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x j x)) * Gmat⁻¹) := by
          rw [Matrix.trace_mul_comm]
    _ =
        ∑ i : Fin (Module.finrank Real E),
          ∑ j : Fin (Module.finrank Real E),
            ((-2 : Real) *
              Ric t x
                (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x i x)
                (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x j x)) * Gmat⁻¹ j i := by
          simp [Matrix.trace, Matrix.mul_apply]
    _ =
        (-2 : Real) *
          (∑ i : Fin (Module.finrank Real E),
            ∑ j : Fin (Module.finrank Real E),
              Gmat⁻¹ i j *
                Ric t x
                  (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x i x)
                  (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x j x)) := by
          simp_rw [hInvSymm]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro j hj
          ring
    _ = (-2 : Real) * scalar t x := by
          rw [scalar_trace_eq_volume_trace_components
            (I := I) (M := M) (G.metric t) (Ric t) (scalar t) hScalar x]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.traceTimeDerivMetricAt_eq_neg_two_scalar_of_metricDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.traceTimeDerivMetricAt_eq_neg_two_scalar_of_metricDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.traceTimeDerivMetricAt_eq_neg_two_scalar_of_metricDeriv ``Submission.DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.traceTimeDerivMetricAt_eq_neg_two_scalar_of_metricDeriv

theorem volume_variation_ricciFlow_at
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real)
    (scalar : Real → M → Real)
    {f : Real → M → Real} {t₀ : Real}
    (hg : MetricFamilyRegularAt (I := I)
      (metricFamilyForMeasure (I := I) (M := M) G) t₀)
    (hf : FunctionRegularAt f t₀)
    (htrace :
      ∀ x : M, traceTimeDerivMetricAt (I := I) G t₀ x =
        (-2 : Real) * scalar t₀ x) :
    HasDerivAt
      (fun s : Real => ∫ x, f s x ∂(volumeMeasureFamily (I := I) (M := M) G s))
      (∫ x, (deriv (fun s : Real => f s x) t₀ - scalar t₀ x * f t₀ x)
          ∂(volumeMeasureFamily (I := I) (M := M) G t₀))
      t₀ := by
  have hclean :=
    volume_variation_formula_at (I := I) (M := M) G (f := f) (t₀ := t₀) hg hf
  refine hclean.congr_deriv ?_
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards with x
  have hx := htrace x
  calc
    deriv (fun s : Real => f s x) t₀ +
        (1 / 2 : Real) * traceTimeDerivMetricAt (I := I) G t₀ x * f t₀ x
        =
        deriv (fun s : Real => f s x) t₀ +
          ((1 / 2 : Real) * ((-2 : Real) * scalar t₀ x)) * f t₀ x := by
          rw [hx]
    _ = deriv (fun s : Real => f s x) t₀ - scalar t₀ x * f t₀ x := by
          ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.volume_variation_ricciFlow_at then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.volume_variation_ricciFlow_at"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.volume_variation_ricciFlow_at ``Submission.DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.volume_variation_ricciFlow_at

theorem volume_variation_ricciFlow_at_of_metricVariationEquation
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (td : TimeDerivativeData Real A Real)
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real)
    (Ric : DifferentialGeometry.PDE.RicciFlow.RicciTensorField (I := I) (M := M) Real)
    (scalar : Real → M → Real)
    {f : Real → M → Real} {t₀ : Real}
    (hdt : ∀ (F : Real → Real) (t : Real), td.dtApply F t = deriv F t)
    (hEq : DifferentialGeometry.PDE.RicciFlow.MetricVariationEquation (I := I) td G Ric)
    (hScalar : DifferentialGeometry.Geometry.Curvature.scalarRealizesRicciTraceInFrame (I := I)
      (scalar t₀) (Ric t₀)
      (volumeTraceInvMetricComponents (I := I) (M := M) (G.metric t₀))
      (volumeTraceFrame (I := I) (M := M)))
    (hg : MetricFamilyRegularAt (I := I)
      (metricFamilyForMeasure (I := I) (M := M) G) t₀)
    (hf : FunctionRegularAt f t₀) :
    HasDerivAt
      (fun s : Real => ∫ x, f s x ∂(volumeMeasureFamily (I := I) (M := M) G s))
      (∫ x, (deriv (fun s : Real => f s x) t₀ - scalar t₀ x * f t₀ x)
          ∂(volumeMeasureFamily (I := I) (M := M) G t₀))
      t₀ := by
  refine volume_variation_ricciFlow_at (I := I) (M := M) G scalar hg hf ?_
  intro x
  exact traceTimeDerivMetricAt_eq_neg_two_scalar_of_scalarTrace
    (I := I) (M := M) td G Ric scalar hdt hEq (t := t₀) hScalar x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.volume_variation_ricciFlow_at_of_metricVariationEquation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.volume_variation_ricciFlow_at_of_metricVariationEquation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.volume_variation_ricciFlow_at_of_metricVariationEquation ``Submission.DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.volume_variation_ricciFlow_at_of_metricVariationEquation

theorem volume_variation_ricciFlow_at_of_metricDeriv
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real)
    (Ric : DifferentialGeometry.PDE.RicciFlow.RicciTensorField (I := I) (M := M) Real)
    (scalar : Real → M → Real)
    {f : Real → M → Real} {t₀ : Real}
    (hEq : DifferentialGeometry.PDE.RicciFlow.MetricVariationEquationDerivAt (I := I) G Ric
      t₀)
    (hScalar : DifferentialGeometry.Geometry.Curvature.scalarRealizesRicciTraceInFrame (I := I)
      (scalar t₀) (Ric t₀)
      (volumeTraceInvMetricComponents (I := I) (M := M) (G.metric t₀))
      (volumeTraceFrame (I := I) (M := M)))
    (hg : MetricFamilyRegularAt (I := I)
      (metricFamilyForMeasure (I := I) (M := M) G) t₀)
    (hf : FunctionRegularAt f t₀) :
    HasDerivAt
      (fun s : Real => ∫ x, f s x ∂(volumeMeasureFamily (I := I) (M := M) G s))
      (∫ x, (deriv (fun s : Real => f s x) t₀ - scalar t₀ x * f t₀ x)
          ∂(volumeMeasureFamily (I := I) (M := M) G t₀))
      t₀ := by
  refine volume_variation_ricciFlow_at (I := I) (M := M) G scalar hg hf ?_
  intro x
  exact traceTimeDerivMetricAt_eq_neg_two_scalar_of_metricDeriv
    (I := I) (M := M) G Ric scalar hEq hScalar x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.volume_variation_ricciFlow_at_of_metricDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.volume_variation_ricciFlow_at_of_metricDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.volume_variation_ricciFlow_at_of_metricDeriv ``Submission.DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.volume_variation_ricciFlow_at_of_metricDeriv

theorem volume_variation_ricciFlow_at_of_metricDeriv_canonicalScalar
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real)
    (Ric : DifferentialGeometry.PDE.RicciFlow.RicciTensorField (I := I) (M := M) Real)
    {f : Real → M → Real} {t₀ : Real}
    (hEq : DifferentialGeometry.PDE.RicciFlow.MetricVariationEquationDerivAt (I := I) G Ric
      t₀)
    (hg : MetricFamilyRegularAt (I := I)
      (metricFamilyForMeasure (I := I) (M := M) G) t₀)
    (hf : FunctionRegularAt f t₀) :
    HasDerivAt
      (fun s : Real => ∫ x, f s x ∂(volumeMeasureFamily (I := I) (M := M) G s))
      (∫ x, (deriv (fun s : Real => f s x) t₀ -
            scalarCurvatureFromRicciInVolumeFrame (I := I) (M := M) G Ric t₀ x * f t₀ x)
          ∂(volumeMeasureFamily (I := I) (M := M) G t₀))
      t₀ :=
  volume_variation_ricciFlow_at_of_metricDeriv
    (I := I) (M := M) G Ric
    (scalarCurvatureFromRicciInVolumeFrame (I := I) (M := M) G Ric)
    hEq
    (scalarCurvatureFromRicciInVolumeFrame_realizes (I := I) (M := M) G Ric t₀)
    hg hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.volume_variation_ricciFlow_at_of_metricDeriv_canonicalScalar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.volume_variation_ricciFlow_at_of_metricDeriv_canonicalScalar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.volume_variation_ricciFlow_at_of_metricDeriv_canonicalScalar ``Submission.DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.volume_variation_ricciFlow_at_of_metricDeriv_canonicalScalar

theorem total_volume_variation_ricciFlow_at_of_metricDeriv
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real)
    (Ric : DifferentialGeometry.PDE.RicciFlow.RicciTensorField (I := I) (M := M) Real)
    {t₀ : Real}
    (hEq : DifferentialGeometry.PDE.RicciFlow.MetricVariationEquationDerivAt (I := I) G Ric
      t₀)
    (hg : MetricFamilyRegularAt (I := I)
      (metricFamilyForMeasure (I := I) (M := M) G) t₀) :
    HasDerivAt
      (fun s : Real => ∫ _x, (1 : Real) ∂(volumeMeasureFamily (I := I) (M := M) G s))
      (∫ x, - scalarCurvatureFromRicciInVolumeFrame (I := I) (M := M) G Ric t₀ x
          ∂(volumeMeasureFamily (I := I) (M := M) G t₀))
      t₀ := by
  simpa [deriv_const] using
    (volume_variation_ricciFlow_at_of_metricDeriv_canonicalScalar
      (I := I) (M := M) G Ric (f := fun _ : Real => fun _ : M => (1 : Real))
      hEq hg (FunctionRegularAt_one (M := M) t₀))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.total_volume_variation_ricciFlow_at_of_metricDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.total_volume_variation_ricciFlow_at_of_metricDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.total_volume_variation_ricciFlow_at_of_metricDeriv ``Submission.DifferentialGeometry.PDE.RicciFlow.Evolution.Volume.total_volume_variation_ricciFlow_at_of_metricDeriv

end Volume
end Evolution
end DifferentialGeometry.PDE.RicciFlow
