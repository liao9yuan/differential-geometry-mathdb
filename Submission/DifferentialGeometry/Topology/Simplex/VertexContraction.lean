import Submission.DifferentialGeometry.Topology.Simplex.Face
import Mathlib.Topology.Homotopy.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.Simplex

variable {I J : Type*} [Fintype I] [Fintype J]

def vertexContraction [DecidableEq I] (i : I) :
    C(unitInterval × stdSimplex ℝ I, stdSimplex ℝ I) := by
  exact ⟨fun z => ⟨(1 - (z.1 : ℝ)) • z.2.val + (z.1 : ℝ) • (stdSimplex.vertex (S := ℝ) i).val,
    convex_stdSimplex ℝ I z.2.property (stdSimplex.vertex (S := ℝ) i).property
      (sub_nonneg.mpr z.1.property.2) z.1.property.1 (sub_add_cancel _ _)⟩, by
    apply Continuous.subtype_mk
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp continuous_snd)).add
      ((continuous_subtype_val.comp continuous_fst).smul continuous_const)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.vertexContraction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.vertexContraction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.vertexContraction ``Submission.DifferentialGeometry.Simplex.vertexContraction

theorem vertexContraction_apply [DecidableEq I] (i : I) (t : unitInterval) (q : stdSimplex ℝ I) (j : I) :
    (vertexContraction i (t, q)).val j =
      (1 - (t : ℝ)) * q.val j + (t : ℝ) * if i = j then 1 else 0 := by
  simp [vertexContraction, Pi.single_apply, eq_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.vertexContraction_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.vertexContraction_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.vertexContraction_apply ``Submission.DifferentialGeometry.Simplex.vertexContraction_apply

@[simp] theorem vertexContraction_zero [DecidableEq I] (i : I) (q : stdSimplex ℝ I) :
    vertexContraction i (0, q) = q := by
  apply Subtype.ext
  simp [vertexContraction]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.vertexContraction_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.vertexContraction_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.vertexContraction_zero ``Submission.DifferentialGeometry.Simplex.vertexContraction_zero

@[simp] theorem vertexContraction_one [DecidableEq I] (i : I) (q : stdSimplex ℝ I) :
    vertexContraction i (1, q) = stdSimplex.vertex (S := ℝ) i := by
  apply Subtype.ext
  simp [vertexContraction]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.vertexContraction_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.vertexContraction_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.vertexContraction_one ``Submission.DifferentialGeometry.Simplex.vertexContraction_one

@[simp] theorem vertexContraction_vertex [DecidableEq I] (i : I) (t : unitInterval) :
    vertexContraction i (t, stdSimplex.vertex (S := ℝ) i) = stdSimplex.vertex (S := ℝ) i := by
  apply Subtype.ext
  funext j
  by_cases h : i = j <;> simp [vertexContraction, h]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.vertexContraction_vertex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.vertexContraction_vertex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.vertexContraction_vertex ``Submission.DifferentialGeometry.Simplex.vertexContraction_vertex

theorem vertexContraction_map [DecidableEq I] [DecidableEq J] (f : I → J) (i : I) (t : unitInterval)
    (q : stdSimplex ℝ I) :
    vertexContraction (f i) (t, stdSimplex.map f q) =
      stdSimplex.map f (vertexContraction i (t, q)) := by
  apply Subtype.ext
  change (1 - (t : ℝ)) • FunOnFinite.linearMap ℝ ℝ f q.val +
      (t : ℝ) • (stdSimplex.vertex (S := ℝ) (f i)).val =
      FunOnFinite.linearMap ℝ ℝ f
        ((1 - (t : ℝ)) • q.val + (t : ℝ) • (stdSimplex.vertex (S := ℝ) i).val)
  rw [map_add, map_smul, map_smul]
  have h := congrArg Subtype.val (stdSimplex.map_vertex (S := ℝ) f i)
  exact congrArg (fun v => (1 - (t : ℝ)) • FunOnFinite.linearMap ℝ ℝ f q.val +
    (t : ℝ) • v) h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.vertexContraction_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.vertexContraction_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.vertexContraction_map ``Submission.DifferentialGeometry.Simplex.vertexContraction_map

end DifferentialGeometry.Simplex
