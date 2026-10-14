import Submission.DifferentialGeometry.Geometry.Neck.NormalizedDatum
import Submission.DifferentialGeometry.Geometry.Curvature.OpenEmbeddingPullback
import Submission.DifferentialGeometry.Geometry.Metric.RoundCylinder

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Metric _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.Geometry.Neck

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.E3 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.S2 target :: scope.openDecls } }
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.IC target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Neck.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Neck.instNeZeroNatFinrankRealProdEuclideanSpaceFinOfNat_differentialGeometry : NeZero
    (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ)) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.instNeZeroNatFinrankRealProdEuclideanSpaceFinOfNat_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.instNeZeroNatFinrankRealProdEuclideanSpaceFinOfNat_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Neck.instSigmaCompactSpaceSubtypeProdElemE3S2RealMemOpens (O : _root_.TopologicalSpace.Opens (S2 × ℝ)) : SigmaCompactSpace O :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen IC O.isOpen)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.instSigmaCompactSpaceSubtypeProdElemE3S2RealMemOpens
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.instSigmaCompactSpaceSubtypeProdElemE3S2RealMemOpens target :: scope.openDecls } }

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem abs_scalar_ratio_sub_one_le_of_cylinder_pullback_enorm_lt
    [BoundarylessManifold I M]
    (O : _root_.TopologicalSpace.Opens (S2 × ℝ)) (g : SmoothRiemannianMetric I M) (f : O → M)
    (hf : IsLocalDiffeomorph IC I ∞ f) (hinj : _root_.Function.Injective f)
    (q : ℝ) (hq : 0 < q) (K : Set O) (k : ℕ) (hk : 2 ≤ k)
    (η : ℝ) (hη : η ≤ 1 / 2)
    (hsmall : metricDerivENormSupOn K k
      (pullbackMetricOfInjectiveLocalDiffeomorph (scaleMetric q hq g) f hf hinj)
      ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen O)
      ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen O) < ENNReal.ofReal η)
    (x : O) (hx : x ∈ K) :
    |metricScalarAt g (f x) / q - 1| ≤ 4323 * η := by
  have h := abs_scalar_curvature_restricted_roundCylinder_sub_one_le O
    (pullbackMetricOfInjectiveLocalDiffeomorph (scaleMetric q hq g) f hf hinj) x η hη
    (fun j hj => (metricDerivNorm_lt_of_sup_lt K k _ _ _ hsmall (hj.trans hk) hx).le)
  rw [metricScalarAt_pullbackMetricOfInjectiveLocalDiffeomorph_scale] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.abs_scalar_ratio_sub_one_le_of_cylinder_pullback_enorm_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.abs_scalar_ratio_sub_one_le_of_cylinder_pullback_enorm_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.abs_scalar_ratio_sub_one_le_of_cylinder_pullback_enorm_lt ``Submission.DifferentialGeometry.Geometry.Neck.abs_scalar_ratio_sub_one_le_of_cylinder_pullback_enorm_lt

namespace normalizedDatum

variable [Fact (Module.finrank ℝ E = 3)] [I.Boundaryless]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}

theorem normalizedMetric_scalar (d : normalizedDatum g x₀ δ k)
    (x : bufferedCylinder δ) :
    metricScalarAt d.normalizedMetric x = metricScalarAt g (d.map x) / metricScalarAt g x₀ := by
  rw [normalizedMetric, metricScalarAt_pullbackMetricOfInjectiveLocalDiffeomorph_scale]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.normalizedMetric_scalar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.normalizedMetric_scalar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.normalizedMetric_scalar ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.normalizedMetric_scalar

theorem normalizedMetric_scalar_center (d : normalizedDatum g x₀ δ k) :
    metricScalarAt d.normalizedMetric (cylinderCenter δ d.precision_pos) = 1 := by
  rw [d.normalizedMetric_scalar, d.center_eq, div_self (ne_of_gt d.scalar_pos)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.normalizedMetric_scalar_center then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.normalizedMetric_scalar_center"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.normalizedMetric_scalar_center ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.normalizedMetric_scalar_center

theorem abs_scalar_ratio_sub_one_le (d : normalizedDatum g x₀ δ k)
    (hk : 2 ≤ k) (hδ : δ ≤ 1 / 2) (x : bufferedCylinder δ)
    (hx : x ∈ controlledCylinder δ) :
    |metricScalarAt g (d.map x) / metricScalarAt g x₀ - 1| ≤ 4323 * δ := by
  have h := abs_scalar_curvature_restricted_roundCylinder_sub_one_le
    (bufferedCylinder δ) d.normalizedMetric x δ hδ
    (fun j hj => (metricDerivNorm_lt_of_sup_lt (controlledCylinder δ) k _ _ _
      d.normalizedMetric_error_lt (hj.trans hk) hx).le)
  rw [d.normalizedMetric_scalar] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.abs_scalar_ratio_sub_one_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.abs_scalar_ratio_sub_one_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.abs_scalar_ratio_sub_one_le ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.abs_scalar_ratio_sub_one_le

theorem scalar_pos_of_controlled (d : normalizedDatum g x₀ δ k)
    (hk : 2 ≤ k) (hsmall : 4323 * δ < 1) (x : bufferedCylinder δ)
    (hx : x ∈ controlledCylinder δ) : 0 < metricScalarAt g (d.map x) := by
  have hδ : δ ≤ 1 / 2 := by linarith [d.precision_pos]
  have h := (abs_le.mp (d.abs_scalar_ratio_sub_one_le hk hδ x hx)).1
  have hratio : 0 < metricScalarAt g (d.map x) / metricScalarAt g x₀ := by linarith
  exact (div_pos_iff_of_pos_right d.scalar_pos).mp hratio

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.scalar_pos_of_controlled then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.scalar_pos_of_controlled"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.scalar_pos_of_controlled ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.scalar_pos_of_controlled

end normalizedDatum
end DifferentialGeometry.Geometry.Neck
