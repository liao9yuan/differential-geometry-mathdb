import Submission.DifferentialGeometry.Analysis.Normed.Matrix.CovectorBilinear
import Submission.DifferentialGeometry.Topology.UniformConvergence.Composition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Instances.Matrix

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.BigOperators _root_.Matrix.Norms.Elementwise

noncomputable section

namespace Matrix
open _root_.Matrix

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

open _root_.Matrix in
private local instance covectorNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.Matrix.covectorNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Matrix.covectorNormedAddCommGroup target :: scope.openDecls } }

open _root_.Matrix in
private local instance covectorNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.Matrix.covectorNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Matrix.covectorNormedSpace target :: scope.openDecls } }

open _root_.Matrix in
private local instance covectorDualNormedAddCommGroup : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.Matrix.covectorDualNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Matrix.covectorDualNormedAddCommGroup target :: scope.openDecls } }

open _root_.Matrix in
private local instance covectorDualNormedSpace : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.Matrix.covectorDualNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Matrix.covectorDualNormedSpace target :: scope.openDecls } }

open _root_.Matrix in
private local instance covectorBilinearNormedAddCommGroup : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.Matrix.covectorBilinearNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Matrix.covectorBilinearNormedAddCommGroup target :: scope.openDecls } }

open _root_.Matrix in
private local instance covectorBilinearNormedSpace : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.Matrix.covectorBilinearNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Matrix.covectorBilinearNormedSpace target :: scope.openDecls } }

open _root_.Matrix in
def weightedInvCovectorBilin (b : ι → E) (p : ℝ × Matrix ι ι ℝ) :
    (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ :=
  (p.1 * Real.sqrt p.2.det) • covectorBilin b p.2⁻¹

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Matrix.weightedInvCovectorBilin then
    throwError "Refusing to shadow existing declaration Matrix.weightedInvCovectorBilin"
  Lean.modifyEnv fun env => Lean.addAlias env `Matrix.weightedInvCovectorBilin ``Submission.Matrix.weightedInvCovectorBilin

open _root_.Matrix in
@[simp] theorem weightedInvCovectorBilin_apply (b : ι → E)
    (p : ℝ × Matrix ι ι ℝ) (u v : E →L[ℝ] ℝ) :
    weightedInvCovectorBilin b p u v =
      (p.1 * Real.sqrt p.2.det) * (∑ i, ∑ j, p.2⁻¹ i j * u (b j) * v (b i)) := by
  simp [weightedInvCovectorBilin]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Matrix.weightedInvCovectorBilin_apply then
    throwError "Refusing to shadow existing declaration Matrix.weightedInvCovectorBilin_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `Matrix.weightedInvCovectorBilin_apply ``Submission.Matrix.weightedInvCovectorBilin_apply

open _root_.Matrix in
theorem continuousAt_weightedInvCovectorBilin (b : ι → E)
    {p : ℝ × Matrix ι ι ℝ} (hp : p.2.det ≠ 0) :
    ContinuousAt (weightedInvCovectorBilin b) p := by
  have hinv : ContinuousAt (fun A : Matrix ι ι ℝ => A⁻¹) p.2 := by
    apply continuousAt_matrix_inv _
    rw [Ring.inverse_eq_inv']
    exact continuousAt_id.inv₀ hp
  have hbilin : ContinuousAt
      (fun q : ℝ × Matrix ι ι ℝ => covectorBilin b q.2⁻¹) p :=
    (covectorBilin b).continuous.continuousAt.comp
      (hinv.comp continuous_snd.continuousAt)
  exact (continuous_fst.continuousAt.mul
    (Real.continuous_sqrt.comp continuous_snd.matrix_det).continuousAt).smul hbilin

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Matrix.continuousAt_weightedInvCovectorBilin then
    throwError "Refusing to shadow existing declaration Matrix.continuousAt_weightedInvCovectorBilin"
  Lean.modifyEnv fun env => Lean.addAlias env `Matrix.continuousAt_weightedInvCovectorBilin ``Submission.Matrix.continuousAt_weightedInvCovectorBilin

end Matrix

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private local instance covectorNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.covectorNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `covectorNormedAddCommGroup target :: scope.openDecls } }

private local instance covectorNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.covectorNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `covectorNormedSpace target :: scope.openDecls } }

private local instance covectorDualNormedAddCommGroup : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.covectorDualNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `covectorDualNormedAddCommGroup target :: scope.openDecls } }

private local instance covectorDualNormedSpace : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.covectorDualNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `covectorDualNormedSpace target :: scope.openDecls } }

private local instance covectorBilinearNormedAddCommGroup : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.covectorBilinearNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `covectorBilinearNormedAddCommGroup target :: scope.openDecls } }

private local instance covectorBilinearNormedSpace : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.covectorBilinearNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `covectorBilinearNormedSpace target :: scope.openDecls } }

open _root_.TendstoUniformlyOn in
theorem TendstoUniformlyOn.weightedInvCovectorBilin
    {ι P N : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → E) {X : N → P → ℝ × Matrix ι ι ℝ}
    {v : P → ℝ × Matrix ι ι ℝ} {l : Filter N} {K : Set P}
    (hX : TendstoUniformlyOn X v l K) (hK : IsCompact (v '' K))
    (hdet : ∀ z ∈ K, (v z).2.det ≠ 0) :
    TendstoUniformlyOn (fun n z => Matrix.weightedInvCovectorBilin b (X n z))
      (fun z => Matrix.weightedInvCovectorBilin b (v z)) l K := by
  apply hX.comp_continuousAt_of_isCompact_image hK
  rintro p ⟨z, hz, rfl⟩
  exact Matrix.continuousAt_weightedInvCovectorBilin b (hdet z hz)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `TendstoUniformlyOn.weightedInvCovectorBilin then
    throwError "Refusing to shadow existing declaration TendstoUniformlyOn.weightedInvCovectorBilin"
  Lean.modifyEnv fun env => Lean.addAlias env `TendstoUniformlyOn.weightedInvCovectorBilin ``Submission.TendstoUniformlyOn.weightedInvCovectorBilin

end
