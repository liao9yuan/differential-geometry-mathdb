import Submission.DifferentialGeometry.Geometry.Neck.InsertionOrientation
import Submission.DifferentialGeometry.Geometry.Neck.Recentering

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.TopologicalSpace _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Metric
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff
namespace DifferentialGeometry.Geometry.Neck.normalizedDatum
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k j : ℕ}

def lowerOrder (d : normalizedDatum g x₀ δ k) (hjk : j ≤ k) : normalizedDatum g x₀ δ j where
  precision_pos := d.precision_pos
  precision_lt_one := d.precision_lt_one
  map := d.map
  smooth := d.smooth
  injective := d.injective
  immersion := d.immersion
  center_eq := d.center_eq
  scalar_pos := d.scalar_pos
  retainedSide := d.retainedSide
  error_lt := (metricDerivENormSupOn_mono (subset_refl _) hjk _ _ _).trans_lt d.error_lt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.lowerOrder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.lowerOrder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.lowerOrder ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.lowerOrder

theorem lowerOrder_map (d : normalizedDatum g x₀ δ k) (hjk : j ≤ k) :
    (d.lowerOrder hjk).map = d.map := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.lowerOrder_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.lowerOrder_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.lowerOrder_map ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.lowerOrder_map

theorem lowerOrder_retainedSide (d : normalizedDatum g x₀ δ k) (hjk : j ≤ k) :
    (d.lowerOrder hjk).retainedSide = d.retainedSide := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.lowerOrder_retainedSide then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.lowerOrder_retainedSide"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.lowerOrder_retainedSide ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.lowerOrder_retainedSide

theorem lowerOrder_normalizedMetric (d : normalizedDatum g x₀ δ k) (hjk : j ≤ k) :
    (d.lowerOrder hjk).normalizedMetric = d.normalizedMetric := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.lowerOrder_normalizedMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.lowerOrder_normalizedMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.lowerOrder_normalizedMetric ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.lowerOrder_normalizedMetric

theorem lowerOrder_controlledMap (d : normalizedDatum g x₀ δ k) (hjk : j ≤ k) :
    (d.lowerOrder hjk).controlledMap = d.controlledMap := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.lowerOrder_controlledMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.lowerOrder_controlledMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.lowerOrder_controlledMap ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.lowerOrder_controlledMap

theorem lowerOrder_controlledImage (d : normalizedDatum g x₀ δ k) (hjk : j ≤ k) :
    (d.lowerOrder hjk).controlledImage = d.controlledImage := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.lowerOrder_controlledImage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.lowerOrder_controlledImage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.lowerOrder_controlledImage ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.lowerOrder_controlledImage

theorem lowerOrder_oriented (d : normalizedDatum g x₀ δ k) (hjk : j ≤ k) :
    (d.lowerOrder hjk).oriented = d.oriented.lowerOrder hjk := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.lowerOrder_oriented then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.lowerOrder_oriented"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.lowerOrder_oriented ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.lowerOrder_oriented

theorem lowerOrder_rescaled (d : normalizedDatum g x₀ δ k) (hjk : j ≤ k) (c : ℝ) (hc : 0 < c) :
    (d.lowerOrder hjk).rescaled c hc = (d.rescaled c hc).lowerOrder hjk := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.lowerOrder_rescaled then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.lowerOrder_rescaled"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.lowerOrder_rescaled ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.lowerOrder_rescaled

theorem lowerOrder_offsetPoint (d : normalizedDatum g x₀ δ k) (hjk : j ≤ k)
    {σ : ℝ} (hσ : σ ^ 2 = 1) :
    (d.lowerOrder hjk).offsetPoint hσ = d.offsetPoint hσ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.lowerOrder_offsetPoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.lowerOrder_offsetPoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.lowerOrder_offsetPoint ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.lowerOrder_offsetPoint

end DifferentialGeometry.Geometry.Neck.normalizedDatum
