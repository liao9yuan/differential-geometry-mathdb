import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Covering
import Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderQuotients

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal _root_.Topology
open _root_.Submission.DifferentialGeometry.Integral.Measure
  (riemannianVolumeMeasure_map_eq_natCast_smul_of_localPullMetric)

namespace DifferentialGeometry.Geometry

local notation "Cylinder" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ
local notation "CylinderI" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

section

private local instance cylinderMeasurableSpace : MeasurableSpace Cylinder := borel Cylinder

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.cylinderMeasurableSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.cylinderMeasurableSpace target :: scope.openDecls } }
private local instance cylinderBorelSpace : BorelSpace Cylinder := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.cylinderBorelSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.cylinderBorelSpace target :: scope.openDecls } }
private local instance quotientMeasurableSpace : MeasurableSpace CylinderDiagonalQuotient :=
  borel CylinderDiagonalQuotient

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.quotientMeasurableSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.quotientMeasurableSpace target :: scope.openDecls } }
private local instance quotientBorelSpace : BorelSpace CylinderDiagonalQuotient := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.quotientBorelSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.quotientBorelSpace target :: scope.openDecls } }

private theorem encard_cylinderDiagonalQuotientMap_fiber (y : CylinderDiagonalQuotient) :
    {x : Cylinder | cylinderDiagonalQuotientMap x = y}.encard = (2 : ℕ∞) := by
  classical
  revert y
  refine Quotient.ind (motive := fun y : CylinderDiagonalQuotient =>
    {x : Cylinder | cylinderDiagonalQuotientMap x = y}.encard = (2 : ℕ∞)) fun x₀ => ?_
  have hfix : x₀ ≠ cylinderDiagonalDiffeomorph x₀ := by
    intro h
    exact cylinderDiagonalDiffeomorph_fixed_point_free x₀ h.symm
  have hset : {x : Cylinder | cylinderDiagonalQuotientMap x =
      cylinderDiagonalQuotientMap x₀} = {x₀, cylinderDiagonalDiffeomorph x₀} := by
    ext x
    rw [Set.mem_ofPred_eq, cylinderDiagonalQuotientMap_eq_iff]
    exact ⟨fun h => h, fun h => h⟩
  change {x : Cylinder | cylinderDiagonalQuotientMap x =
    cylinderDiagonalQuotientMap x₀}.encard = (2 : ℕ∞)
  rw [hset, Set.encard_insert_of_notMem (by simpa using hfix),
    Set.encard_singleton]
  norm_num

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.encard_cylinderDiagonalQuotientMap_fiber
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.encard_cylinderDiagonalQuotientMap_fiber target :: scope.openDecls } }

theorem map_cylinderDiagonalQuotientMap_riemannianVolumeMeasure :
    Measure.map cylinderDiagonalQuotientMap
        (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
          (I := CylinderI) (M := Cylinder)
          roundThreeCylinderShrinkerMetric) =
      (2 : ENNReal) •
        DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
          (I := CylinderI) (M := CylinderDiagonalQuotient) cylinderDiagonalQuotientMetric :=
  riemannianVolumeMeasure_map_eq_natCast_smul_of_localPullMetric
    (I := CylinderI) (M := Cylinder) (N := CylinderDiagonalQuotient)
    roundThreeCylinderShrinkerMetric cylinderDiagonalQuotientMetric
    cylinderDiagonalQuotientMap_isLocalDiffeomorph
    localPullMetric_cylinderDiagonalQuotientMetric 2 encard_cylinderDiagonalQuotientMap_fiber

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.map_cylinderDiagonalQuotientMap_riemannianVolumeMeasure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.map_cylinderDiagonalQuotientMap_riemannianVolumeMeasure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.map_cylinderDiagonalQuotientMap_riemannianVolumeMeasure ``Submission.DifferentialGeometry.Geometry.map_cylinderDiagonalQuotientMap_riemannianVolumeMeasure

end

end DifferentialGeometry.Geometry
