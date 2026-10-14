import Mathlib.Geometry.Manifold.Diffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Set _root_.Function
open scoped _root_.Manifold _root_.ContDiff
namespace DifferentialGeometry.Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]

private theorem writtenInExtChartAt_id_transContinuousLinearEquiv_apply
    (e : E ≃L[𝕜] F) (x : N) (y : F) :
    writtenInExtChartAt (I.transContinuousLinearEquiv e) I x (id : N → N) y =
      (extChartAt I x) ((extChartAt I x).symm (e.symm y)) := by
  simp only [writtenInExtChartAt, Function.comp_apply, id_eq,
    ModelWithCorners.coe_extChartAt_transContinuousLinearEquiv_symm]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Manifold.writtenInExtChartAt_id_transContinuousLinearEquiv_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Manifold.writtenInExtChartAt_id_transContinuousLinearEquiv_apply target :: scope.openDecls } }

private theorem writtenInExtChartAt_id_transContinuousLinearEquiv_eqOn
    (e : E ≃L[𝕜] F) (x : N) :
    Set.EqOn (writtenInExtChartAt (I.transContinuousLinearEquiv e) I x (id : N → N))
      (fun y : F => e.symm y) (extChartAt (I.transContinuousLinearEquiv e) x).target := by
  intro y hy
  rw [writtenInExtChartAt_id_transContinuousLinearEquiv_apply]
  have hy' : e.symm y ∈ (extChartAt I x).target := by
    rwa [ModelWithCorners.extChartAt_transContinuousLinearEquiv_target] at hy
  exact (extChartAt I x).right_inv hy'

run_cmd do
  let target := ``Submission.DifferentialGeometry.Manifold.writtenInExtChartAt_id_transContinuousLinearEquiv_eqOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Manifold.writtenInExtChartAt_id_transContinuousLinearEquiv_eqOn target :: scope.openDecls } }

private theorem hasFDerivWithinAt_writtenInExtChartAt_id_transContinuousLinearEquiv
    (e : E ≃L[𝕜] F) (x : N) :
    HasFDerivWithinAt
      (writtenInExtChartAt (I.transContinuousLinearEquiv e) I x (id : N → N))
      e.symm.toContinuousLinearMap (_root_.Set.range (I.transContinuousLinearEquiv e))
      ((extChartAt (I.transContinuousLinearEquiv e) x) x) := by
  have hbase : HasFDerivWithinAt (fun y : F => e.symm y) e.symm.toContinuousLinearMap
      (_root_.Set.range (I.transContinuousLinearEquiv e))
      ((extChartAt (I.transContinuousLinearEquiv e) x) x) :=
    e.symm.hasFDerivWithinAt
  have hpoint : (writtenInExtChartAt (I.transContinuousLinearEquiv e) I x (id : N → N))
      ((extChartAt (I.transContinuousLinearEquiv e) x) x) =
      e.symm ((extChartAt (I.transContinuousLinearEquiv e) x) x) :=
    writtenInExtChartAt_id_transContinuousLinearEquiv_eqOn (I := I) e x (mem_extChartAt_target x)
  refine hbase.congr_of_eventuallyEq ?_ hpoint
  rw [Filter.EventuallyEq,
    ← nhdsWithin_extChartAt_target_eq (I := I.transContinuousLinearEquiv e) x]
  exact eventually_nhdsWithin_iff.mpr (Filter.Eventually.of_forall fun _ hy =>
    writtenInExtChartAt_id_transContinuousLinearEquiv_eqOn (I := I) e x hy)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Manifold.hasFDerivWithinAt_writtenInExtChartAt_id_transContinuousLinearEquiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Manifold.hasFDerivWithinAt_writtenInExtChartAt_id_transContinuousLinearEquiv target :: scope.openDecls } }

theorem mfderiv_id_transContinuousLinearEquiv (e : E ≃L[𝕜] F) (x : N) :
    mfderiv (I.transContinuousLinearEquiv e) I (id : N → N) x = e.symm.toContinuousLinearMap :=
  HasMFDerivAt.mfderiv (f := (id : N → N))
    ⟨continuousAt_id,
      hasFDerivWithinAt_writtenInExtChartAt_id_transContinuousLinearEquiv (I := I) e x⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.mfderiv_id_transContinuousLinearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.mfderiv_id_transContinuousLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.mfderiv_id_transContinuousLinearEquiv ``Submission.DifferentialGeometry.Manifold.mfderiv_id_transContinuousLinearEquiv


variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 G H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]

theorem mfderiv_transContinuousLinearEquiv (I : ModelWithCorners 𝕜 E H)
    (e : E ≃L[𝕜] F)
    {f : N → M} {x : N} (hf : MDifferentiableAt I J f x) :
    mfderiv (I.transContinuousLinearEquiv e) J f x =
      (mfderiv I J f x).comp e.symm.toContinuousLinearMap := by
  let Phi := (ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞) I N e).symm
  have hPhi := Phi.mdifferentiable (by simp : (∞ : WithTop ℕ∞) ≠ 0) x
  have h := mfderiv_comp x hf hPhi
  change mfderiv (I.transContinuousLinearEquiv e) J f x =
    (mfderiv I J f x).comp (mfderiv (I.transContinuousLinearEquiv e) I id x) at h
  rw [mfderiv_id_transContinuousLinearEquiv] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.mfderiv_transContinuousLinearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.mfderiv_transContinuousLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.mfderiv_transContinuousLinearEquiv ``Submission.DifferentialGeometry.Manifold.mfderiv_transContinuousLinearEquiv

variable {G' : Type*} [NormedAddCommGroup G'] [NormedSpace 𝕜 G']

theorem mfderiv_transContinuousLinearEquiv_naturality
    (e : E ≃L[𝕜] F) (f : G ≃L[𝕜] G')
    {g : N → M} {x : N} (hg : MDifferentiableAt I J g x) :
    f.symm.toContinuousLinearMap.comp
        (mfderiv (I.transContinuousLinearEquiv e) (J.transContinuousLinearEquiv f) g x) =
      (mfderiv I J g x).comp e.symm.toContinuousLinearMap := by
  let Phi := (ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞) I N e).symm
  let Psi := ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞) J M f
  have hPsi := Psi.symm.mdifferentiable (by simp : (∞ : WithTop ℕ∞) ≠ 0) (g x)
  have hg' : MDifferentiableAt (I.transContinuousLinearEquiv e) (J.transContinuousLinearEquiv f) g x :=
    (Psi.mdifferentiable (by simp) (g x)).comp x
      (hg.comp x (Phi.mdifferentiable (by simp) x))
  have h := mfderiv_comp x hPsi hg'
  change mfderiv (I.transContinuousLinearEquiv e) J g x =
    (mfderiv (J.transContinuousLinearEquiv f) J id (g x)).comp
      (mfderiv (I.transContinuousLinearEquiv e) (J.transContinuousLinearEquiv f) g x) at h
  rw [mfderiv_id_transContinuousLinearEquiv, mfderiv_transContinuousLinearEquiv I e hg] at h
  exact h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.mfderiv_transContinuousLinearEquiv_naturality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.mfderiv_transContinuousLinearEquiv_naturality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.mfderiv_transContinuousLinearEquiv_naturality ``Submission.DifferentialGeometry.Manifold.mfderiv_transContinuousLinearEquiv_naturality

end DifferentialGeometry.Manifold
