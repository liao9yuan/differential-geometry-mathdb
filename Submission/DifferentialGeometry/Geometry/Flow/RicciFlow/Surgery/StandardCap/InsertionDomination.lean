import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.InsertionMetric
import Submission.DifferentialGeometry.Geometry.Metric.BilinearPerturbation
import Submission.DifferentialGeometry.Geometry.Metric.RoundCylinder

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Bundle _root_.Submission.Bundle _root_.TopologicalSpace _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Metric
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.E3 target :: scope.openDecls } }
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.IC target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }

theorem exp_two_conformalFactor_le_one (z : ℝ) :
    Real.exp (2 * conformalFactor z) ≤ 1 := by
  rw [exp_two_conformalFactor]
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hp : 0 < warpingFunction (conformalRadius z) / Real.sqrt 2 :=
    div_pos (warpingFunction_pos (conformalRadius_pos z)) hs
  have hu : warpingFunction (conformalRadius z) / Real.sqrt 2 ≤ 1 :=
    (div_le_one hs).mpr (warpingFunction_le_sqrt_two _)
  nlinarith [mul_nonneg (sub_nonneg.mpr hu) (by linarith :
    0 ≤ 1 + warpingFunction (conformalRadius z) / Real.sqrt 2)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.exp_two_conformalFactor_le_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.exp_two_conformalFactor_le_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.exp_two_conformalFactor_le_one ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.exp_two_conformalFactor_le_one

private theorem original_mem {A B : ℝ} (hAB : 2 * A < B)
    (q : insertionCylinder A B) : q.val ∈ DifferentialGeometry.Geometry.Neck.openCylinder B := by
  change -B < q.val.2 ∧ q.val.2 < B
  exact ⟨by have hz := q.property.1; linarith, q.property.2⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.original_mem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.original_mem target :: scope.openDecls } }

theorem insertedMetric_inner_le_of_cylinder_lower {A B η : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B))
    (q : insertionCylinder A B) (v : TangentSpace IC q)
    (hlower : η * (roundCylinderMetric (E := E3) (n := 2)).inner q.val v v ≤
      h.inner ⟨q.val, original_mem hAB q⟩ v v) :
    (insertedMetric hA hAB hη h).inner (insertionMap hA hAB q)
      (mfderiv IC (𝓡 3) (insertionMap hA hAB) q v)
      (mfderiv IC (𝓡 3) (insertionMap hA hAB) q v) ≤
      h.inner ⟨q.val, original_mem hAB q⟩ v v := by
  rw [insertedMetric_interpolation]
  have hc : 0 ≤ insertionCutoff A q.val.2 ∧ insertionCutoff A q.val.2 ≤ 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hpos := metric_inner_self_nonneg h
    (⟨q.val, original_mem hAB q⟩) v
  have hcomb := mul_le_mul_of_nonneg_left hlower (sub_nonneg.mpr hc.2)
  have hexp := Real.exp_pos (2 * conformalFactor q.val.2)
  have hfactor := exp_two_conformalFactor_le_one q.val.2
  have hblend : insertionCutoff A q.val.2 *
      h.inner ⟨q.val, original_mem hAB q⟩ v v +
      (1 - insertionCutoff A q.val.2) * η *
        (roundCylinderMetric (E := E3) (n := 2)).inner q.val v v ≤
      h.inner ⟨q.val, original_mem hAB q⟩ v v := by
    nlinarith
  exact (mul_le_mul_of_nonneg_left hblend hexp.le).trans
    (mul_le_of_le_one_left hpos hfactor)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertedMetric_inner_le_of_cylinder_lower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.insertedMetric_inner_le_of_cylinder_lower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertedMetric_inner_le_of_cylinder_lower ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertedMetric_inner_le_of_cylinder_lower

theorem insertedMetric_inner_le_of_metricDerivNorm_le {A B δ : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hδ : 0 ≤ δ) (hδ1 : δ < 1)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B))
    (q : insertionCylinder A B)
    (herr : metricDerivNorm 0 h
      ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen
        (DifferentialGeometry.Geometry.Neck.openCylinder B))
      ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen
        (DifferentialGeometry.Geometry.Neck.openCylinder B))
      ⟨q.val, original_mem hAB q⟩ ≤ δ)
    (v : TangentSpace IC q) :
    (insertedMetric hA hAB
      (sub_pos.mpr ((Real.sqrt_lt hδ zero_le_one).mpr (by simpa using hδ1))) h).inner
      (insertionMap hA hAB q)
      (mfderiv IC (𝓡 3) (insertionMap hA hAB) q v)
      (mfderiv IC (𝓡 3) (insertionMap hA hAB) q v) ≤
      h.inner ⟨q.val, original_mem hAB q⟩ v v := by
  apply insertedMetric_inner_le_of_cylinder_lower
  have hb := (inner_bounds_of_metricDerivNorm_le
    ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen
      (DifferentialGeometry.Geometry.Neck.openCylinder B)) h _ herr v).1
  have hnn := metric_inner_self_nonneg (roundCylinderMetric (E := E3) (n := 2)) q.val v
  have hs : δ ≤ Real.sqrt δ := by
    have hsq := Real.sq_sqrt hδ
    have hlo := Real.sqrt_nonneg δ
    have hhi := (Real.sqrt_lt hδ zero_le_one).mpr (by simpa using hδ1)
    nlinarith [mul_nonneg hlo (sub_nonneg.mpr hhi.le)]
  change (1 - δ) * (roundCylinderMetric (E := E3) (n := 2)).inner q.val v v ≤ _ at hb
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_left hs 1) hnn).trans hb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertedMetric_inner_le_of_metricDerivNorm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.insertedMetric_inner_le_of_metricDerivNorm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertedMetric_inner_le_of_metricDerivNorm_le ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertedMetric_inner_le_of_metricDerivNorm_le

end DifferentialGeometry.PDE.RicciFlow.StandardCap
