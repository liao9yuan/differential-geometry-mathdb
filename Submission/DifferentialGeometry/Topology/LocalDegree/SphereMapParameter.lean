import Submission.DifferentialGeometry.Topology.LocalDegree.SphereMap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.Metric _root_.Set
open scoped _root_.unitInterval
noncomputable section
namespace DifferentialGeometry.LocalDegree
variable {E F K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
  (f : E → F) (x : E) (R : ℝ)
  (hf : ContinuousOn f (closedBall x R))
  (hz : ∀ y ∈ closedBall x R, y ≠ x → f y ≠ 0)


def sphereMapParameter (r : C(K, _root_.Set.Ioc (0 : ℝ) R)) (v : C(K, _root_.Metric.sphere (0 : E) 1)) :
    C(K, _root_.Metric.sphere (0 : F) 1) :=
  (sphereMapFamily f x R hf hz).comp
    ⟨fun z => (r z, v z), r.continuous.prodMk v.continuous⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.sphereMapParameter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.sphereMapParameter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.sphereMapParameter ``Submission.DifferentialGeometry.LocalDegree.sphereMapParameter


@[simp]
theorem sphereMapParameter_apply (r : C(K, _root_.Set.Ioc (0 : ℝ) R))
    (v : C(K, _root_.Metric.sphere (0 : E) 1)) (z : K) :
    (sphereMapParameter f x R hf hz r v z : F) =
      ‖f (x + (r z : ℝ) • (v z : E))‖⁻¹ • f (x + (r z : ℝ) • (v z : E)) :=
  sphereMapFamily_apply f x R hf hz (r z) (v z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.sphereMapParameter_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.sphereMapParameter_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.sphereMapParameter_apply ``Submission.DifferentialGeometry.LocalDegree.sphereMapParameter_apply


@[simp]
theorem sphereMapParameter_const (r : _root_.Set.Ioc (0 : ℝ) R) (v : C(K, _root_.Metric.sphere (0 : E) 1)) :
    sphereMapParameter f x R hf hz (ContinuousMap.const K r) v =
      (sphereMap f x R hf hz r).comp v := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.sphereMapParameter_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.sphereMapParameter_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.sphereMapParameter_const ``Submission.DifferentialGeometry.LocalDegree.sphereMapParameter_const

private def interpolatedRadius (r₀ r₁ : C(K, _root_.Set.Ioc (0 : ℝ) R)) :
    C(I × K, _root_.Set.Ioc (0 : ℝ) R) where
  toFun p := ⟨(1 - (p.1 : ℝ)) * (r₀ p.2 : ℝ) + (p.1 : ℝ) * (r₁ p.2 : ℝ),
    (convex_Ioc (0 : ℝ) R) (r₀ p.2).property (r₁ p.2).property
      (sub_nonneg.mpr p.1.property.2) p.1.property.1 (sub_add_cancel _ _)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      (continuous_subtype_val.comp (r₀.continuous.comp continuous_snd))).add
      ((continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp (r₁.continuous.comp continuous_snd)))

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.interpolatedRadius
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.interpolatedRadius target :: scope.openDecls } }

def sphereMapParameterHomotopy (r₀ r₁ : C(K, _root_.Set.Ioc (0 : ℝ) R))
    (v : C(K, _root_.Metric.sphere (0 : E) 1)) :
    (sphereMapParameter f x R hf hz r₀ v).Homotopy
      (sphereMapParameter f x R hf hz r₁ v) where
  toFun p := sphereMapFamily f x R hf hz (interpolatedRadius R r₀ r₁ p, v p.2)
  continuous_toFun := (sphereMapFamily f x R hf hz).continuous.comp
    ((interpolatedRadius R r₀ r₁).continuous.prodMk (v.continuous.comp continuous_snd))
  map_zero_left z := by
    change sphereMapFamily f x R hf hz (interpolatedRadius R r₀ r₁ (0, z), v z) =
      sphereMapFamily f x R hf hz (r₀ z, v z)
    congr 1
    apply Prod.ext
    · apply Subtype.ext
      simp [interpolatedRadius]
    · rfl
  map_one_left z := by
    change sphereMapFamily f x R hf hz (interpolatedRadius R r₀ r₁ (1, z), v z) =
      sphereMapFamily f x R hf hz (r₁ z, v z)
    congr 1
    apply Prod.ext
    · apply Subtype.ext
      simp [interpolatedRadius]
    · rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.sphereMapParameterHomotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.sphereMapParameterHomotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.sphereMapParameterHomotopy ``Submission.DifferentialGeometry.LocalDegree.sphereMapParameterHomotopy


@[simp]
theorem sphereMapParameterHomotopy_apply (r₀ r₁ : C(K, _root_.Set.Ioc (0 : ℝ) R))
    (v : C(K, _root_.Metric.sphere (0 : E) 1)) (t : I) (z : K) :
    (sphereMapParameterHomotopy f x R hf hz r₀ r₁ v (t, z) : F) =
      ‖f (x + ((1 - (t : ℝ)) * (r₀ z : ℝ) + (t : ℝ) * (r₁ z : ℝ)) • (v z : E))‖⁻¹ •
        f (x + ((1 - (t : ℝ)) * (r₀ z : ℝ) + (t : ℝ) * (r₁ z : ℝ)) • (v z : E)) :=
  sphereMapFamily_apply f x R hf hz (interpolatedRadius R r₀ r₁ (t, z)) (v z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.sphereMapParameterHomotopy_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.sphereMapParameterHomotopy_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.sphereMapParameterHomotopy_apply ``Submission.DifferentialGeometry.LocalDegree.sphereMapParameterHomotopy_apply

end DifferentialGeometry.LocalDegree
