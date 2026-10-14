import Submission.DifferentialGeometry.Tensor.RSTensor.Defs
import Submission.DifferentialGeometry.Tensor.Multilinear.Bundle.Fiber
import Submission.DifferentialGeometry.Tensor.Multilinear.Bundle.Defs
import Submission.DifferentialGeometry.Bundle.TangentSpace
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.IsManifold _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap
open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry
namespace Tensor

open _root_.Submission.DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private lemma achart_eq_of_chartAt_eq {b b₀ : M}
    (h_chart : chartAt H b = chartAt H b₀) :
    achart H b = achart H b₀ :=
  Subtype.ext h_chart

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.achart_eq_of_chartAt_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.achart_eq_of_chartAt_eq target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private lemma tangent_trivb₀_symmL_eq_id_of_chartAt_eq
    {b b₀ : M} (h_chart : chartAt H b = chartAt H b₀)
    (hb : b ∈ (chartAt H b₀).source) :
    (_root_.FiberBundle.trivializationAt E (TangentSpace I) b₀).symmL ℝ b =
      (tangentSpaceModelContinuousLinearEquiv (I := I) b).symm.toContinuousLinearMap := by
  rw [TangentBundle.symmL_trivializationAt_eq_core (𝕜 := ℝ) (I := I)
    (b₀ := b₀) (b := b) hb]
  rw [achart_eq_of_chartAt_eq (H := H) (M := M) h_chart]
  ext v
  apply (tangentBundleCore I M).coordChange_self (achart H b₀) b
  rw [tangentBundleCore_baseSet, coe_achart]
  exact hb

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.tangent_trivb₀_symmL_eq_id_of_chartAt_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.tangent_trivb₀_symmL_eq_id_of_chartAt_eq target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private lemma tangent_trivb₀_clmAt_eq_id_of_chartAt_eq
    {b b₀ : M} (h_chart : chartAt H b = chartAt H b₀)
    (hb : b ∈ (chartAt H b₀).source) :
    (_root_.FiberBundle.trivializationAt E (TangentSpace I) b₀).continuousLinearMapAt ℝ b =
      (tangentSpaceModelContinuousLinearEquiv (I := I) b).toContinuousLinearMap := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
    (𝕜 := ℝ) (I := I) (b₀ := b₀) (b := b) hb]
  rw [achart_eq_of_chartAt_eq (H := H) (M := M) h_chart]
  ext v
  apply (tangentBundleCore I M).coordChange_self (achart H b₀) b
  rw [tangentBundleCore_baseSet, coe_achart]
  exact hb

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.tangent_trivb₀_clmAt_eq_id_of_chartAt_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.tangent_trivb₀_clmAt_eq_id_of_chartAt_eq target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private lemma tangent_trivializationAt_baseSet (b₀ : M) :
    (_root_.FiberBundle.trivializationAt E (TangentSpace I) b₀).baseSet = (chartAt H b₀).source :=
  TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) b₀

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.tangent_trivializationAt_baseSet
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.tangent_trivializationAt_baseSet target :: scope.openDecls } }

theorem triv_continuousLinearMapAt_eq_compContinuousLinearMap
    {s : ℕ} (b₀ b : M)
    (hb : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) b₀).baseSet)
    (T : Bundle.continuousMultilinearMap ℝ s E (TangentSpace I) b) :
    ((_root_.FiberBundle.trivializationAt
        (ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ)
        (Bundle.continuousMultilinearMap ℝ s E (TangentSpace I)) b₀).continuousLinearMapAt
          ℝ b T :
        ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) =
      T.compContinuousLinearMap
        (fun _ : Fin s => (_root_.FiberBundle.trivializationAt E (TangentSpace I) b₀).symmL ℝ b) := by
  set e := _root_.FiberBundle.trivializationAt
    (ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ)
    (Bundle.continuousMultilinearMap ℝ s E (TangentSpace I)) b₀ with he_def
  have hbase : b ∈ e.baseSet := hb
  have h_cLMA : (e.continuousLinearMapAt ℝ b T :
      ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) =
      (e ⟨b, T⟩).2 := by
    have h := congrFun (e.coe_linearMapAt_of_mem (R := ℝ) hbase) T
    simpa [Bundle.Trivialization.continuousLinearMapAt_apply] using h
  rw [h_cLMA]
  apply ContinuousMultilinearMap.ext
  intro w
  change T (fun i : Fin s => (_root_.FiberBundle.trivializationAt E (TangentSpace I) b₀).symmL ℝ b (w i)) = _
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.triv_continuousLinearMapAt_eq_compContinuousLinearMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.triv_continuousLinearMapAt_eq_compContinuousLinearMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.triv_continuousLinearMapAt_eq_compContinuousLinearMap ``Submission.DifferentialGeometry.Tensor.triv_continuousLinearMapAt_eq_compContinuousLinearMap

theorem multilinear_trivAt_symmL_apply_eq_self_on_locality
    (s : ℕ) (b₀ : M) {b : M}
    (h_chart : chartAt H b = chartAt H b₀)
    (h_source : b ∈ (chartAt H b₀).source)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    ((_root_.FiberBundle.trivializationAt (ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ)
        (Bundle.continuousMultilinearMap ℝ s E (TangentSpace I)) b₀).symmL ℝ b T :
        ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) = T := by
  have h_base : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) b₀).baseSet := by
    rw [tangent_trivializationAt_baseSet (I := I) b₀]
    exact h_source
  have h_clmAt_id := tangent_trivb₀_clmAt_eq_id_of_chartAt_eq (I := I) (M := M)
    h_chart h_source
  rw [Bundle.continuousMultilinearMap.triv_symmL_eq_compContinuousLinearMap
    (𝕜 := ℝ) (F := E) (E := (TangentSpace I : M → Type _)) (s := s) b₀ b h_base T]
  rw [h_clmAt_id]
  apply ContinuousMultilinearMap.ext
  intro v
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.multilinear_trivAt_symmL_apply_eq_self_on_locality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.multilinear_trivAt_symmL_apply_eq_self_on_locality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.multilinear_trivAt_symmL_apply_eq_self_on_locality ``Submission.DifferentialGeometry.Tensor.multilinear_trivAt_symmL_apply_eq_self_on_locality

theorem multilinear_trivAt_continuousLinearMapAt_apply_eq_self_on_locality
    (s : ℕ) (b₀ : M) {b : M}
    (h_chart : chartAt H b = chartAt H b₀)
    (h_source : b ∈ (chartAt H b₀).source)
    (T : Bundle.continuousMultilinearMap ℝ s E (TangentSpace I) b) :
    ((_root_.FiberBundle.trivializationAt (ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ)
        (Bundle.continuousMultilinearMap ℝ s E (TangentSpace I)) b₀).continuousLinearMapAt
          ℝ b T :
        ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) =
      (T : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) := by
  have h_base : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) b₀).baseSet := by
    rw [tangent_trivializationAt_baseSet (I := I) b₀]
    exact h_source
  have h_symmL_id := tangent_trivb₀_symmL_eq_id_of_chartAt_eq (I := I) (M := M)
    h_chart h_source
  rw [triv_continuousLinearMapAt_eq_compContinuousLinearMap (I := I)
    (s := s) b₀ b h_base T]
  rw [h_symmL_id]
  apply ContinuousMultilinearMap.ext
  intro v
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.multilinear_trivAt_continuousLinearMapAt_apply_eq_self_on_locality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.multilinear_trivAt_continuousLinearMapAt_apply_eq_self_on_locality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.multilinear_trivAt_continuousLinearMapAt_apply_eq_self_on_locality ``Submission.DifferentialGeometry.Tensor.multilinear_trivAt_continuousLinearMapAt_apply_eq_self_on_locality

theorem tensor0S_trivAt_symmL_eq_one_on_locality
    (s : ℕ) (b₀ : M) {b : M}
    (h_chart : chartAt H b = chartAt H b₀)
    (h_source : b ∈ (chartAt H b₀).source)
    (T : Tensor0SModel s ℝ E) :
    ((_root_.FiberBundle.trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) b₀).symmL ℝ b T :
        ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) = T := by
  change (_root_.FiberBundle.trivializationAt
      (ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ)
      (Bundle.continuousMultilinearMap ℝ s E (TangentSpace I)) b₀).symmL ℝ b T = T
  exact multilinear_trivAt_symmL_apply_eq_self_on_locality
    (s := s) (b₀ := b₀) (b := b) (h_chart := h_chart) (h_source := h_source) (T := T)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.tensor0S_trivAt_symmL_eq_one_on_locality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.tensor0S_trivAt_symmL_eq_one_on_locality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.tensor0S_trivAt_symmL_eq_one_on_locality ``Submission.DifferentialGeometry.Tensor.tensor0S_trivAt_symmL_eq_one_on_locality

theorem tensor0S_trivAt_continuousLinearMapAt_eq_one_on_locality
    (s : ℕ) (b₀ : M) {b : M}
    (h_chart : chartAt H b = chartAt H b₀)
    (h_source : b ∈ (chartAt H b₀).source)
    (T : Tensor0SSpace s I b) :
    ((_root_.FiberBundle.trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) b₀).continuousLinearMapAt ℝ b T :
        ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) =
      (T : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) := by
  change (_root_.FiberBundle.trivializationAt
      (ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ)
      (Bundle.continuousMultilinearMap ℝ s E (TangentSpace I)) b₀).continuousLinearMapAt
        ℝ b T = T
  exact multilinear_trivAt_continuousLinearMapAt_apply_eq_self_on_locality
    (s := s) (b₀ := b₀) (b := b) (h_chart := h_chart) (h_source := h_source) (T := T)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.tensor0S_trivAt_continuousLinearMapAt_eq_one_on_locality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.tensor0S_trivAt_continuousLinearMapAt_eq_one_on_locality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.tensor0S_trivAt_continuousLinearMapAt_eq_one_on_locality ``Submission.DifferentialGeometry.Tensor.tensor0S_trivAt_continuousLinearMapAt_eq_one_on_locality

end Tensor
end DifferentialGeometry

end
