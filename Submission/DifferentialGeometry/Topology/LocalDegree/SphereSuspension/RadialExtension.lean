import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.Metric _root_.Set
noncomputable section
namespace DifferentialGeometry.LocalDegree
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private def radialExtensionFun (f : C(_root_.Metric.sphere (0 : E) 1, _root_.Metric.sphere (0 : F) 1)) (x : E) : F := by
  classical
  exact if hx : x = 0 then 0 else
    ‖x‖ • (f ((homeomorphUnitSphereProd E) ⟨x, hx⟩).1 : F)

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.radialExtensionFun
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.radialExtensionFun target :: scope.openDecls } }

private theorem radialExtensionFun_zero (f : C(_root_.Metric.sphere (0 : E) 1, _root_.Metric.sphere (0 : F) 1)) :
    radialExtensionFun f 0 = 0 := by simp [radialExtensionFun]

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.radialExtensionFun_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.radialExtensionFun_zero target :: scope.openDecls } }

private theorem radialExtensionFun_norm (f : C(_root_.Metric.sphere (0 : E) 1, _root_.Metric.sphere (0 : F) 1)) (x : E) :
    ‖radialExtensionFun f x‖ = ‖x‖ := by
  by_cases hx : x = 0
  · simp [radialExtensionFun, hx]
  · simp [radialExtensionFun, hx, norm_smul, norm_eq_of_mem_sphere]

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.radialExtensionFun_norm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.radialExtensionFun_norm target :: scope.openDecls } }

private theorem continuous_radialExtensionFun (f : C(_root_.Metric.sphere (0 : E) 1, _root_.Metric.sphere (0 : F) 1)) :
    Continuous (radialExtensionFun f) := by
  have hc : ContinuousOn (radialExtensionFun f) ({0}ᶜ : Set E) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : ({0}ᶜ : Set E).domRestrict (radialExtensionFun f) =
        fun x : ({0}ᶜ : Set E) ↦ ‖x.val‖ • (f ((homeomorphUnitSphereProd E) x).1 : F) := by
      funext x
      exact dif_neg (show x.val ≠ 0 from x.property)
    rw [heq]
    exact (continuous_norm.comp continuous_subtype_val).smul
      (continuous_subtype_val.comp (f.continuous.comp (homeomorphUnitSphereProd E).continuous.fst))
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst x
    rw [ContinuousAt, radialExtensionFun_zero, tendsto_zero_iff_norm_tendsto_zero]
    simpa only [ContinuousAt, radialExtensionFun_norm, norm_zero] using (continuous_norm.continuousAt (x := (0 : E)))
  · exact hc.continuousAt (isOpen_compl_singleton.mem_nhds hx)

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.continuous_radialExtensionFun
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.continuous_radialExtensionFun target :: scope.openDecls } }


def sphereRadialExtension (f : C(_root_.Metric.sphere (0 : E) 1, _root_.Metric.sphere (0 : F) 1)) : C(E, F) :=
  ⟨radialExtensionFun f, continuous_radialExtensionFun f⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.sphereRadialExtension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.sphereRadialExtension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.sphereRadialExtension ``Submission.DifferentialGeometry.LocalDegree.sphereRadialExtension


@[simp]
theorem sphereRadialExtension_zero (f : C(_root_.Metric.sphere (0 : E) 1, _root_.Metric.sphere (0 : F) 1)) :
    sphereRadialExtension f 0 = 0 := radialExtensionFun_zero f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.sphereRadialExtension_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.sphereRadialExtension_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.sphereRadialExtension_zero ``Submission.DifferentialGeometry.LocalDegree.sphereRadialExtension_zero


@[simp]
theorem sphereRadialExtension_norm (f : C(_root_.Metric.sphere (0 : E) 1, _root_.Metric.sphere (0 : F) 1)) (x : E) :
    ‖sphereRadialExtension f x‖ = ‖x‖ := radialExtensionFun_norm f x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.sphereRadialExtension_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.sphereRadialExtension_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.sphereRadialExtension_norm ``Submission.DifferentialGeometry.LocalDegree.sphereRadialExtension_norm


theorem sphereRadialExtension_apply_of_ne_zero (f : C(_root_.Metric.sphere (0 : E) 1, _root_.Metric.sphere (0 : F) 1))
    {x : E} (hx : x ≠ 0) :
    sphereRadialExtension f x = ‖x‖ • (f ((homeomorphUnitSphereProd E) ⟨x, hx⟩).1 : F) :=
  dif_neg hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.sphereRadialExtension_apply_of_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.sphereRadialExtension_apply_of_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.sphereRadialExtension_apply_of_ne_zero ``Submission.DifferentialGeometry.LocalDegree.sphereRadialExtension_apply_of_ne_zero


@[simp]
theorem sphereRadialExtension_sphere (f : C(_root_.Metric.sphere (0 : E) 1, _root_.Metric.sphere (0 : F) 1))
    (v : _root_.Metric.sphere (0 : E) 1) : sphereRadialExtension f v = f v := by
  rw [sphereRadialExtension_apply_of_ne_zero f (ne_zero_of_mem_unit_sphere v),
    norm_eq_of_mem_sphere v, one_smul]
  congr 2
  apply Subtype.ext
  rw [homeomorphUnitSphereProd_apply_fst_coe, norm_eq_of_mem_sphere v]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.sphereRadialExtension_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.sphereRadialExtension_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.sphereRadialExtension_sphere ``Submission.DifferentialGeometry.LocalDegree.sphereRadialExtension_sphere
end DifferentialGeometry.LocalDegree
