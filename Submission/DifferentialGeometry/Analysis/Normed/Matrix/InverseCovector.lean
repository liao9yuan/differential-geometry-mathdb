import Submission.DifferentialGeometry.Analysis.Normed.Matrix.CovectorBilinear
import Submission.DifferentialGeometry.Topology.UniformConvergence.Composition
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

variable {𝕜 ι E : Type*} [NontriviallyNormedField 𝕜] [Fintype ι] [DecidableEq ι]
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
private local instance covectorBilinNormedAddCommGroup :
    NormedAddCommGroup ((E →L[𝕜] 𝕜) →L[𝕜] (E →L[𝕜] 𝕜) →L[𝕜] 𝕜) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.Matrix.covectorBilinNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Matrix.covectorBilinNormedAddCommGroup target :: scope.openDecls } }

open _root_.Matrix in
private local instance covectorBilinNormedSpace :
    NormedSpace 𝕜 ((E →L[𝕜] 𝕜) →L[𝕜] (E →L[𝕜] 𝕜) →L[𝕜] 𝕜) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.Matrix.covectorBilinNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Matrix.covectorBilinNormedSpace target :: scope.openDecls } }

open _root_.Matrix in
theorem continuousAt_smul_covectorBilin_inv (b : ι → E)
    {p : 𝕜 × Matrix ι ι 𝕜} (hp : p.2.det ≠ 0) :
    ContinuousAt (fun q : 𝕜 × Matrix ι ι 𝕜 => q.1 • covectorBilin b q.2⁻¹) p := by
  have hinv : ContinuousAt (fun A : Matrix ι ι 𝕜 => A⁻¹) p.2 := by
    apply continuousAt_matrix_inv _
    rw [Ring.inverse_eq_inv']
    exact continuousAt_id.inv₀ hp
  have hbilin : ContinuousAt
      (fun q : 𝕜 × Matrix ι ι 𝕜 => covectorBilin b q.2⁻¹) p :=
    (covectorBilin b).continuous.continuousAt.comp
      (hinv.comp continuous_snd.continuousAt)
  exact continuous_fst.continuousAt.smul hbilin

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Matrix.continuousAt_smul_covectorBilin_inv then
    throwError "Refusing to shadow existing declaration Matrix.continuousAt_smul_covectorBilin_inv"
  Lean.modifyEnv fun env => Lean.addAlias env `Matrix.continuousAt_smul_covectorBilin_inv ``Submission.Matrix.continuousAt_smul_covectorBilin_inv

end Matrix

section

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

private local instance covectorNormedAddCommGroup : NormedAddCommGroup (E →L[𝕜] 𝕜) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.covectorNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `covectorNormedAddCommGroup target :: scope.openDecls } }

private local instance covectorNormedSpace : NormedSpace 𝕜 (E →L[𝕜] 𝕜) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.covectorNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `covectorNormedSpace target :: scope.openDecls } }

private local instance covectorDualNormedAddCommGroup : NormedAddCommGroup ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.covectorDualNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `covectorDualNormedAddCommGroup target :: scope.openDecls } }

private local instance covectorDualNormedSpace : NormedSpace 𝕜 ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.covectorDualNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `covectorDualNormedSpace target :: scope.openDecls } }

private local instance covectorBilinNormedAddCommGroup :
    NormedAddCommGroup ((E →L[𝕜] 𝕜) →L[𝕜] (E →L[𝕜] 𝕜) →L[𝕜] 𝕜) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.covectorBilinNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `covectorBilinNormedAddCommGroup target :: scope.openDecls } }

private local instance covectorBilinNormedSpace :
    NormedSpace 𝕜 ((E →L[𝕜] 𝕜) →L[𝕜] (E →L[𝕜] 𝕜) →L[𝕜] 𝕜) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.covectorBilinNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `covectorBilinNormedSpace target :: scope.openDecls } }

open _root_.TendstoUniformlyOn in
theorem TendstoUniformlyOn.smul_covectorBilin_inv
    {ι P N : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → E) {X : N → P → 𝕜 × Matrix ι ι 𝕜}
    {v : P → 𝕜 × Matrix ι ι 𝕜} {l : Filter N} {K : Set P}
    (hX : TendstoUniformlyOn X v l K) (hK : IsCompact (v '' K))
    (hdet : ∀ z ∈ K, (v z).2.det ≠ 0) :
    TendstoUniformlyOn (fun n z => (X n z).1 • Matrix.covectorBilin b (X n z).2⁻¹)
      (fun z => (v z).1 • Matrix.covectorBilin b (v z).2⁻¹) l K := by
  apply hX.comp_continuousAt_of_isCompact_image
    (g := fun p : 𝕜 × Matrix ι ι 𝕜 => p.1 • Matrix.covectorBilin b p.2⁻¹) hK
  rintro p ⟨z, hz, rfl⟩
  exact Matrix.continuousAt_smul_covectorBilin_inv b (hdet z hz)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `TendstoUniformlyOn.smul_covectorBilin_inv then
    throwError "Refusing to shadow existing declaration TendstoUniformlyOn.smul_covectorBilin_inv"
  Lean.modifyEnv fun env => Lean.addAlias env `TendstoUniformlyOn.smul_covectorBilin_inv ``Submission.TendstoUniformlyOn.smul_covectorBilin_inv

end
