import Submission.DifferentialGeometry.Geometry.Curvature.Naturality.OpenSubtype
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Iterated.Basic
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Naturality.OpenRestriction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Tensor0SBundle

open _root_.Submission.DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

local instance _root_.Submission.DifferentialGeometry.Tensor0SBundle.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.instCompleteSpace_differentialGeometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.instCompleteSpace_differentialGeometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.instCompleteSpace_differentialGeometry ``Submission.DifferentialGeometry.Tensor0SBundle.instCompleteSpace_differentialGeometry
local instance _root_.Submission.DifferentialGeometry.Tensor0SBundle.instIsManifoldRealOfNatWithTopENat_differentialGeometry : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.instIsManifoldRealOfNatWithTopENat_differentialGeometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.instIsManifoldRealOfNatWithTopENat_differentialGeometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.instIsManifoldRealOfNatWithTopENat_differentialGeometry ``Submission.DifferentialGeometry.Tensor0SBundle.instIsManifoldRealOfNatWithTopENat_differentialGeometry
local instance _root_.Submission.DifferentialGeometry.Tensor0SBundle.instIsManifoldRealOfNatWithTopENat_differentialGeometry_1 : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.instIsManifoldRealOfNatWithTopENat_differentialGeometry_1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.instIsManifoldRealOfNatWithTopENat_differentialGeometry_1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.instIsManifoldRealOfNatWithTopENat_differentialGeometry_1 ``Submission.DifferentialGeometry.Tensor0SBundle.instIsManifoldRealOfNatWithTopENat_differentialGeometry_1

private theorem totalNabla0SFun_metric_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M) (s : ℕ)
    (AU : Tensor0SField (I := I) (M := U) (n := (∞ : WithTop ℕ∞)) s)
    (AM : Tensor0SField (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    (hA : ∀ (x : U) (slots : Fin s → TangentSpace I x), AU x slots = AM (x : M) slots)
    (x : U) (slots : Fin (s + 1) → TangentSpace I x) :
    totalNabla0SFun s (metricCov (g.restrictOpen U)) AU x slots =
      totalNabla0SFun s (metricCov g) AM (x : M) slots := by
  classical
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := TangentSpace I) (n := (⊤ : ℕ∞)) (x : M) (slots 0)
  let V : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    fun q => (ContMDiffSection.exists_eq_at (I := I) (F := E)
      (V := TangentSpace I) (n := (⊤ : ℕ∞)) (x : M) (slots q.succ)).choose
  have hV (q : Fin s) : V q (x : M) = slots q.succ :=
    (ContMDiffSection.exists_eq_at (I := I) (F := E)
      (V := TangentSpace I) (n := (⊤ : ℕ∞)) (x : M) (slots q.succ)).choose_spec
  let XU := restrictOpenTangentSection U X
  let VU := fun q => restrictOpenTangentSection U (V q)
  have hslotsM : (Fin.cons (X (x : M)) (fun q => V q (x : M)) :
      Fin (s + 1) → TangentSpace I (x : M)) = slots := by
    funext q
    refine Fin.cases ?_ (fun p => ?_) q
    · exact hX
    · exact hV p
  have hslotsU : Fin.cons (XU x) (fun q => VU q x) = slots := by
    funext q
    refine Fin.cases ?_ (fun p => ?_) q
    · exact (restrictOpenTangentSection_apply U X x).trans hX
    · exact (restrictOpenTangentSection_apply U (V p) x).trans (hV p)
  have hl := (totalNabla0SFun_apply_section s (metricCov (g.restrictOpen U)) XU AU x
    (fun q => VU q x)).trans (nabla0SFun_eval_smooth_slots _ XU VU AU x)
  have hr := (totalNabla0SFun_apply_section s (metricCov g) X AM (x : M)
    (fun q => V q (x : M))).trans (nabla0SFun_eval_smooth_slots _ X V AM (x : M))
  rw [hslotsU] at hl
  rw [hslotsM] at hr
  rw [hl, hr]
  have hscalar : (fun y : U => AU y (fun q => VU q y)) =
      fun y : U => AM (y : M) (fun q => V q (y : M)) := by
    funext y
    simpa only [VU, restrictOpenTangentSection_apply] using hA y (fun q => VU q y)
  have hf : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => AM y (fun q => V q y)) (x : M) :=
    (tensor0SField_eval_smooth_slots_contMDiffAt AM V (x : M)).mdifferentiableAt (by simp)
  apply congrArg₂ (· - ·)
  · rw [hscalar]
    exact (mvfderiv_restrictOpen U _ x (XU x) hf).trans
      (congrArg (fun v : TangentSpace I (x : M) =>
        mvfderiv (I := I) (fun y : M => AM y (fun q => V q y)) (x : M) v)
        (restrictOpenTangentSection_apply U X x))
  apply Finset.sum_congr rfl
  intro p _
  rw [hA]
  apply congrArg (AM (x : M))
  have hcov := (metricCov_restrictOpen_globalSection g U (V p) x (XU x)).trans
    (congrArg (fun v : TangentSpace I (x : M) =>
      (metricCov g (fun y : M => V p y) (x : M)) v)
      (restrictOpenTangentSection_apply U X x))
  ext q
  by_cases hqp : q = p
  · subst q
    simp only [Function.update_self]
    exact hcov
  · rw [Function.update_of_ne hqp, Function.update_of_ne hqp]
    exact restrictOpenTangentSection_apply U (V q) x

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor0SBundle.totalNabla0SFun_metric_restrictOpen
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor0SBundle.totalNabla0SFun_metric_restrictOpen target :: scope.openDecls } }

theorem totalNabla0SFun_metricCov_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M) (s : ℕ)
    (A : Tensor0SField (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s) (x : U) :
    totalNabla0SFun s (metricCov (g.restrictOpen U)) (restrictOpen0S s A) x =
      totalNabla0SFun s (metricCov g) A (x : M) := by
  ext slots
  exact totalNabla0SFun_metric_restrictOpen g U s _ A (fun _ _ => rfl) x slots

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.totalNabla0SFun_metricCov_restrictOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.totalNabla0SFun_metricCov_restrictOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.totalNabla0SFun_metricCov_restrictOpen ``Submission.DifferentialGeometry.Tensor0SBundle.totalNabla0SFun_metricCov_restrictOpen

end DifferentialGeometry.Tensor0SBundle
