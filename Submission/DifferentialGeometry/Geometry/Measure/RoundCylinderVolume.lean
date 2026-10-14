import Submission.DifferentialGeometry.Geometry.Measure.Product
import Submission.DifferentialGeometry.Geometry.Metric.Sphere.Round.TotalArea
import Submission.DifferentialGeometry.Geometry.Metric.RoundCylinder
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Scaling

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal _root_.Topology _root_.Submission.DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Measure

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.E3 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.S2 target :: scope.openDecls } }
private instance _root_.Submission.DifferentialGeometry.Geometry.Measure.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }
private instance _root_.Submission.DifferentialGeometry.Geometry.Measure.instMeasurableSpaceElemE3S2 : MeasurableSpace S2 := borel S2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.instMeasurableSpaceElemE3S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.instMeasurableSpaceElemE3S2 target :: scope.openDecls } }
private instance _root_.Submission.DifferentialGeometry.Geometry.Measure.instBorelSpaceElemE3S2 : BorelSpace S2 := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.instBorelSpaceElemE3S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.instBorelSpaceElemE3S2 target :: scope.openDecls } }

private theorem cast_measure_apply {X : Type*} {m₁ m₂ : MeasurableSpace X}
    (hm : m₁ = m₂) (μ : @_root_.MeasureTheory.Measure X m₁) (S : Set X) :
    (cast (congrArg (fun m : MeasurableSpace X => @_root_.MeasureTheory.Measure X m) hm) μ) S = μ S := by
  cases hm
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.cast_measure_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.cast_measure_apply target :: scope.openDecls } }

theorem riemannianVolumeMeasure_roundCylinder_interval (a b : ℝ) :
    riemannianVolumeMeasure ((𝓡 2).prod 𝓘(ℝ)) (S2 × ℝ)
      (Metric.roundCylinderMetric (E := E3) (n := 2)) (_root_.Set.univ ×ˢ _root_.Set.Icc a b) =
      ENNReal.ofReal (8 * Real.pi) * ENNReal.ofReal (b - a) := by
  let h := scaleMetric 2 (by norm_num : (0 : ℝ) < 2) (roundMetric (E := E3) (n := 2))
  have hp (y : S2) (s : ℝ) (v w : TangentSpace (𝓡 2) y) (r t : ℝ) :
      (Metric.roundCylinderMetric (E := E3) (n := 2)).inner (y, s) (v, r) (w, t) =
        h.inner y v w + r * t := by
    change (Metric.roundCylinderMetric (E := E3) (n := 2)).inner (y, s)
      ((show EuclideanSpace ℝ (Fin 2) from v), r)
      ((show EuclideanSpace ℝ (Fin 2) from w), t) = _
    exact Metric.cylinderMetric_inner _ (y, s) _ _
  rw [PDE.RicciFlow.Perelman.KappaSolutions.riemannianVolumeMeasure_product_real_of_inner_eq
    h _ hp, cast_measure_apply
      (@BorelSpace.measurable_eq (S2 × ℝ) _ (@Prod.instMeasurableSpace S2 ℝ _ _) inferInstance)]
  rw [Measure.prod_prod, Real.volume_Icc]
  congr 1
  rw [volume_scale_apply]
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := by simp
  rw [hdim, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _) 2, Real.sq_sqrt (by norm_num),
    riemannianVolumeMeasure_roundMetric_sphere_univ_eq, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_roundCylinder_interval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_roundCylinder_interval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_roundCylinder_interval ``Submission.DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_roundCylinder_interval

end DifferentialGeometry.Geometry.Measure
