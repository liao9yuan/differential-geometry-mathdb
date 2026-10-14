import Submission.DifferentialGeometry.Geometry.Metric.Scaling
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem contMDiff_conformalMetric_inner_section
    (g : SmoothRiemannianMetric I M) (u : C^∞⟮I, M; Real⟯) :
    ContMDiff I (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) ∞
      (fun y : M => TotalSpace.mk' (E →L[Real] E →L[Real] Real)
        (E := fun y : M => TangentSpace I y →L[Real] TangentSpace I y →L[Real] Real)
        y (Real.exp (2 * u y) • g.inner y)) := by
  let : (y : M) → TopologicalSpace
      (TangentSpace I y →L[Real] TangentSpace I y →L[Real] Real) := fun _ => inferInstance
  have h : ContMDiff I 𝓘(Real, Real) ∞ (fun x => Real.exp (2 * u x)) :=
    Real.contDiff_exp.contMDiff.comp (contMDiff_const.mul u.contMDiff)
  convert
    h.smul_section (I := I) (F := E →L[Real] E →L[Real] Real)
      (V := fun y : M => TangentSpace I y →L[Real] TangentSpace I y →L[Real] Real)
      g.contMDiff using 1
  with_reducible_and_instances rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.contMDiff_conformalMetric_inner_section
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.contMDiff_conformalMetric_inner_section target :: scope.openDecls } }

def conformalMetric (g : SmoothRiemannianMetric I M) (u : C^∞⟮I, M; Real⟯) :
    SmoothRiemannianMetric I M where
  inner x := Real.exp (2 * u x) • g.inner x
  symm x v w := (scaleMetric (Real.exp (2 * u x)) (Real.exp_pos _) g).symm x v w
  pos x v hv := (scaleMetric (Real.exp (2 * u x)) (Real.exp_pos _) g).pos x v hv
  isVonNBounded x := (scaleMetric (Real.exp (2 * u x)) (Real.exp_pos _) g).isVonNBounded x
  contMDiff := contMDiff_conformalMetric_inner_section g u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.conformalMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.conformalMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.conformalMetric ``Submission.DifferentialGeometry.conformalMetric

@[simp] theorem conformalMetric_inner
    (g : SmoothRiemannianMetric I M) (u : C^∞⟮I, M; Real⟯)
    (x : M) (v w : TangentSpace I x) :
    (conformalMetric g u).inner x v w = Real.exp (2 * u x) * g.inner x v w :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.conformalMetric_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.conformalMetric_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.conformalMetric_inner ``Submission.DifferentialGeometry.conformalMetric_inner

@[simp] theorem conformalMetric_zero (g : SmoothRiemannianMetric I M) :
    conformalMetric g 0 = g := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  change Real.exp (2 * 0) * g.inner x v w = g.inner x v w
  rw [_root_.MulZeroClass.mul_zero, Real.exp_zero, one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.conformalMetric_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.conformalMetric_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.conformalMetric_zero ``Submission.DifferentialGeometry.conformalMetric_zero

theorem conformalMetric_add (g : SmoothRiemannianMetric I M)
    (u v : C^∞⟮I, M; Real⟯) :
    conformalMetric g (u + v) = conformalMetric (conformalMetric g u) v := by
  apply SmoothRiemannianMetric.ext_inner
  intro x a b
  change Real.exp (2 * (u x + v x)) * g.inner x a b =
    Real.exp (2 * v x) * (Real.exp (2 * u x) * g.inner x a b)
  rw [mul_add, Real.exp_add]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.conformalMetric_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.conformalMetric_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.conformalMetric_add ``Submission.DifferentialGeometry.conformalMetric_add

@[simp] theorem conformalMetric_neg (g : SmoothRiemannianMetric I M)
    (u : C^∞⟮I, M; Real⟯) :
    conformalMetric (conformalMetric g u) (-u) = g := by
  rw [← conformalMetric_add, add_neg_cancel, conformalMetric_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.conformalMetric_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.conformalMetric_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.conformalMetric_neg ``Submission.DifferentialGeometry.conformalMetric_neg

theorem conformalMetric_const (g : SmoothRiemannianMetric I M) (c : Real) :
    conformalMetric g (ContMDiffMap.const c) =
      scaleMetric (Real.exp (2 * c)) (Real.exp_pos _) g := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.conformalMetric_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.conformalMetric_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.conformalMetric_const ``Submission.DifferentialGeometry.conformalMetric_const

end DifferentialGeometry
