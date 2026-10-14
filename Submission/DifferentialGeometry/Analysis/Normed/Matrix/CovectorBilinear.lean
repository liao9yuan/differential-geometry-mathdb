import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.BigOperators _root_.Matrix.Norms.Elementwise

noncomputable section

namespace Matrix
open _root_.Matrix

variable {𝕜 ι E : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

open _root_.Matrix in
private local instance covectorNormedAddCommGroup : NormedAddCommGroup (E →L[𝕜] 𝕜) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.Matrix.covectorNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Matrix.covectorNormedAddCommGroup target :: scope.openDecls } }

open _root_.Matrix in
private local instance covectorNormedSpace : NormedSpace 𝕜 (E →L[𝕜] 𝕜) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.Matrix.covectorNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Matrix.covectorNormedSpace target :: scope.openDecls } }

open _root_.Matrix in
private local instance covectorDualNormedAddCommGroup : NormedAddCommGroup ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.Matrix.covectorDualNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Matrix.covectorDualNormedAddCommGroup target :: scope.openDecls } }

open _root_.Matrix in
private local instance covectorDualNormedSpace : NormedSpace 𝕜 ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.Matrix.covectorDualNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Matrix.covectorDualNormedSpace target :: scope.openDecls } }

open _root_.Matrix in
private local instance covectorBilinearNormedAddCommGroup : NormedAddCommGroup ((E →L[𝕜] 𝕜) →L[𝕜] (E →L[𝕜] 𝕜) →L[𝕜] 𝕜) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.Matrix.covectorBilinearNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Matrix.covectorBilinearNormedAddCommGroup target :: scope.openDecls } }

open _root_.Matrix in
private local instance covectorBilinearNormedSpace : NormedSpace 𝕜 ((E →L[𝕜] 𝕜) →L[𝕜] (E →L[𝕜] 𝕜) →L[𝕜] 𝕜) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.Matrix.covectorBilinearNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Matrix.covectorBilinearNormedSpace target :: scope.openDecls } }

open _root_.Matrix in
private def covectorBilinEntry (b : ι → E) (i j : ι) :
    Matrix ι ι 𝕜 →L[𝕜] (E →L[𝕜] 𝕜) →L[𝕜] (E →L[𝕜] 𝕜) →L[𝕜] 𝕜 :=
  ((ContinuousLinearMap.proj j : (ι → 𝕜) →L[𝕜] 𝕜).comp
    (ContinuousLinearMap.proj i : Matrix ι ι 𝕜 →L[𝕜] (ι → 𝕜))).smulRight
      ((ContinuousLinearMap.apply 𝕜 𝕜 (b j)).smulRight
        (ContinuousLinearMap.apply 𝕜 𝕜 (b i)))

run_cmd do
  let target := ``Submission.Matrix.covectorBilinEntry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Matrix.covectorBilinEntry target :: scope.openDecls } }

open _root_.Matrix in
def covectorBilin (b : ι → E) :
    Matrix ι ι 𝕜 →L[𝕜] (E →L[𝕜] 𝕜) →L[𝕜] (E →L[𝕜] 𝕜) →L[𝕜] 𝕜 :=
  ∑ i, ∑ j, covectorBilinEntry b i j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Matrix.covectorBilin then
    throwError "Refusing to shadow existing declaration Matrix.covectorBilin"
  Lean.modifyEnv fun env => Lean.addAlias env `Matrix.covectorBilin ``Submission.Matrix.covectorBilin

open _root_.Matrix in
@[simp] theorem covectorBilin_apply (b : ι → E) (A : Matrix ι ι 𝕜)
    (u v : E →L[𝕜] 𝕜) :
    covectorBilin b A u v = ∑ i, ∑ j, A i j * u (b j) * v (b i) := by
  unfold covectorBilin
  rw [_root_.sum_apply, _root_.sum_apply, _root_.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [_root_.sum_apply, _root_.sum_apply, _root_.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  change A i j * (u (b j) * v (b i)) = _
  exact (mul_assoc _ _ _).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Matrix.covectorBilin_apply then
    throwError "Refusing to shadow existing declaration Matrix.covectorBilin_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `Matrix.covectorBilin_apply ``Submission.Matrix.covectorBilin_apply

end Matrix
