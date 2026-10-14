import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Homotopy.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Metric _root_.Set
open scoped _root_.Topology _root_.unitInterval

noncomputable section

namespace DifferentialGeometry.LocalDegree

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem spherePoint_mem {x : E} {R : ℝ} (r : _root_.Set.Ioc (0 : ℝ) R)
    (v : _root_.Metric.sphere (0 : E) 1) : x + (r : ℝ) • (v : E) ∈ _root_.Metric.sphere x r := by
  rw [_root_.Metric.mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_smul,
    Real.norm_of_nonneg r.property.1.le, norm_eq_of_mem_sphere v, mul_one]

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.spherePoint_mem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.spherePoint_mem target :: scope.openDecls } }

private theorem spherePoint_mem_closedBall {x : E} {R : ℝ} (r : _root_.Set.Ioc (0 : ℝ) R)
    (v : _root_.Metric.sphere (0 : E) 1) : x + (r : ℝ) • (v : E) ∈ _root_.Metric.closedBall x R :=
  _root_.Metric.closedBall_subset_closedBall r.property.2 (_root_.Metric.sphere_subset_closedBall (spherePoint_mem r v))

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.spherePoint_mem_closedBall
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.spherePoint_mem_closedBall target :: scope.openDecls } }

private theorem spherePoint_ne_center {x : E} {R : ℝ} (r : _root_.Set.Ioc (0 : ℝ) R)
    (v : _root_.Metric.sphere (0 : E) 1) : x + (r : ℝ) • (v : E) ≠ x :=
  _root_.Metric.ne_of_mem_sphere (spherePoint_mem r v) r.property.1.ne'

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.spherePoint_ne_center
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.spherePoint_ne_center target :: scope.openDecls } }

def sphereMapFamily (f : E → F) (x : E) (R : ℝ)
    (hf : ContinuousOn f (_root_.Metric.closedBall x R))
    (hzero : ∀ y ∈ _root_.Metric.closedBall x R, y ≠ x → f y ≠ 0) :
    C(_root_.Set.Ioc (0 : ℝ) R × _root_.Metric.sphere (0 : E) 1, _root_.Metric.sphere (0 : F) 1) where
  toFun p := (homeomorphUnitSphereProd F
    ⟨f (x + (p.1 : ℝ) • (p.2 : E)),
      hzero _ (spherePoint_mem_closedBall p.1 p.2) (spherePoint_ne_center p.1 p.2)⟩).1
  continuous_toFun := by
    have hq : Continuous (fun p : _root_.Set.Ioc (0 : ℝ) R × _root_.Metric.sphere (0 : E) 1 ↦
        x + (p.1 : ℝ) • (p.2 : E)) :=
      continuous_const.add ((continuous_subtype_val.comp continuous_fst).smul
        (continuous_subtype_val.comp continuous_snd))
    have hfp := hf.comp_continuous hq (fun p ↦ spherePoint_mem_closedBall p.1 p.2)
    exact (homeomorphUnitSphereProd F).continuous.fst.comp
      (hfp.subtype_mk (fun p ↦
        hzero _ (spherePoint_mem_closedBall p.1 p.2) (spherePoint_ne_center p.1 p.2)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.sphereMapFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.sphereMapFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.sphereMapFamily ``Submission.DifferentialGeometry.LocalDegree.sphereMapFamily


@[simp]
theorem sphereMapFamily_apply (f : E → F) (x : E) (R : ℝ)
    (hf : ContinuousOn f (_root_.Metric.closedBall x R))
    (hzero : ∀ y ∈ _root_.Metric.closedBall x R, y ≠ x → f y ≠ 0)
    (r : _root_.Set.Ioc (0 : ℝ) R) (v : _root_.Metric.sphere (0 : E) 1) :
    (sphereMapFamily f x R hf hzero (r, v) : F) =
      ‖f (x + (r : ℝ) • (v : E))‖⁻¹ • f (x + (r : ℝ) • (v : E)) :=
  homeomorphUnitSphereProd_apply_fst_coe F _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.sphereMapFamily_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.sphereMapFamily_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.sphereMapFamily_apply ``Submission.DifferentialGeometry.LocalDegree.sphereMapFamily_apply


def sphereMap (f : E → F) (x : E) (R : ℝ)
    (hf : ContinuousOn f (_root_.Metric.closedBall x R))
    (hzero : ∀ y ∈ _root_.Metric.closedBall x R, y ≠ x → f y ≠ 0)
    (r : _root_.Set.Ioc (0 : ℝ) R) : C(_root_.Metric.sphere (0 : E) 1, _root_.Metric.sphere (0 : F) 1) :=
  (sphereMapFamily f x R hf hzero).curry r

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.sphereMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.sphereMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.sphereMap ``Submission.DifferentialGeometry.LocalDegree.sphereMap


@[simp]
theorem sphereMap_apply (f : E → F) (x : E) (R : ℝ)
    (hf : ContinuousOn f (_root_.Metric.closedBall x R))
    (hzero : ∀ y ∈ _root_.Metric.closedBall x R, y ≠ x → f y ≠ 0)
    (r : _root_.Set.Ioc (0 : ℝ) R) (v : _root_.Metric.sphere (0 : E) 1) :
    (sphereMap f x R hf hzero r v : F) =
      ‖f (x + (r : ℝ) • (v : E))‖⁻¹ • f (x + (r : ℝ) • (v : E)) :=
  sphereMapFamily_apply f x R hf hzero r v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.sphereMap_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.sphereMap_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.sphereMap_apply ``Submission.DifferentialGeometry.LocalDegree.sphereMap_apply

private def radiusPath {R : ℝ} (r₀ r₁ : _root_.Set.Ioc (0 : ℝ) R) : Path r₀ r₁ where
  toFun t := ⟨Path.segment (r₀ : ℝ) (r₁ : ℝ) t,
    (convex_Ioc (0 : ℝ) R).segment_subset r₀.property r₁.property
      (by rw [← Path.range_segment]; exact _root_.Set.mem_range_self t)⟩
  continuous_toFun := (Path.segment (r₀ : ℝ) (r₁ : ℝ)).continuous.subtype_mk _
  source' := Subtype.ext (Path.source _)
  target' := Subtype.ext (Path.target _)

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.radiusPath
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.radiusPath target :: scope.openDecls } }

def sphereMapHomotopy (f : E → F) (x : E) (R : ℝ)
    (hf : ContinuousOn f (_root_.Metric.closedBall x R))
    (hzero : ∀ y ∈ _root_.Metric.closedBall x R, y ≠ x → f y ≠ 0)
    (r₀ r₁ : _root_.Set.Ioc (0 : ℝ) R) :
    (sphereMap f x R hf hzero r₀).Homotopy (sphereMap f x R hf hzero r₁) where
  toFun p := sphereMapFamily f x R hf hzero (radiusPath r₀ r₁ p.1, p.2)
  continuous_toFun := (sphereMapFamily f x R hf hzero).continuous.comp
    (((radiusPath r₀ r₁).continuous.comp continuous_fst).prodMk continuous_snd)
  map_zero_left v := by simp [sphereMap]
  map_one_left v := by simp [sphereMap]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.sphereMapHomotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.sphereMapHomotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.sphereMapHomotopy ``Submission.DifferentialGeometry.LocalDegree.sphereMapHomotopy

@[simp]
theorem sphereMapHomotopy_apply (f : E → F) (x : E) (R : ℝ)
    (hf : ContinuousOn f (_root_.Metric.closedBall x R))
    (hzero : ∀ y ∈ _root_.Metric.closedBall x R, y ≠ x → f y ≠ 0)
    (r₀ r₁ : _root_.Set.Ioc (0 : ℝ) R) (t : I) (v : _root_.Metric.sphere (0 : E) 1) :
    (sphereMapHomotopy f x R hf hzero r₀ r₁ (t, v) : F) =
      ‖f (x + (((1 - (t : ℝ)) * (r₀ : ℝ) + (t : ℝ) * (r₁ : ℝ)) • (v : E)))‖⁻¹ •
        f (x + (((1 - (t : ℝ)) * (r₀ : ℝ) + (t : ℝ) * (r₁ : ℝ)) • (v : E))) := by
  change (sphereMapFamily f x R hf hzero (radiusPath r₀ r₁ t, v) : F) = _
  simp [radiusPath, Path.segment_apply, AffineMap.lineMap_apply_module]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.sphereMapHomotopy_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.sphereMapHomotopy_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.sphereMapHomotopy_apply ``Submission.DifferentialGeometry.LocalDegree.sphereMapHomotopy_apply

theorem sphereMap_id (R : ℝ) (r : _root_.Set.Ioc (0 : ℝ) R) :
    sphereMap (fun y : E ↦ y) 0 R continuousOn_id (fun _ _ h ↦ h) r =
      ContinuousMap.id (_root_.Metric.sphere (0 : E) 1) := by
  apply ContinuousMap.ext
  intro v
  apply Subtype.ext
  simp only [sphereMap_apply, ContinuousMap.id_apply, zero_add, norm_smul,
    Real.norm_of_nonneg r.property.1.le, norm_eq_of_mem_sphere v, mul_one, smul_smul,
    inv_mul_cancel₀ r.property.1.ne', one_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.sphereMap_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.sphereMap_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.sphereMap_id ``Submission.DifferentialGeometry.LocalDegree.sphereMap_id

end DifferentialGeometry.LocalDegree
