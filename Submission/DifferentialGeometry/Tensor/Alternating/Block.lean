import Submission.DifferentialGeometry.Tensor.Alternating.Composition
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace ContinuousMultilinearMap
open _root_.ContinuousMultilinearMap

noncomputable section

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

open _root_.ContinuousMultilinearMap in
private theorem currySum_domDomCongr_finSumFinEquiv_apply (p q : ℕ)
    (T : ContinuousMultilinearMap 𝕜 (fun _ : Fin (p + q) => E) F)
    (v : Fin p → E) (w : Fin q → E) :
    (T.domDomCongr finSumFinEquiv.symm).currySum v w = T (Fin.append v w) := by
  simp only [_root_.ContinuousMultilinearMap.currySum_apply, _root_.ContinuousMultilinearMap.domDomCongr_apply]
  apply congrArg T
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl, Fin.append_left]
  · rw [finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr, Fin.append_right]

run_cmd do
  let target := ``Submission.ContinuousMultilinearMap.currySum_domDomCongr_finSumFinEquiv_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `ContinuousMultilinearMap.currySum_domDomCongr_finSumFinEquiv_apply target :: scope.openDecls } }

variable [CharZero 𝕜]

open _root_.ContinuousMultilinearMap in
def toBlockAlternating (p q : ℕ)
    (T : ContinuousMultilinearMap 𝕜 (fun _ : Fin (p + q) => E) F)
    (hleft : ∀ (v : Fin p → E) (w : Fin q → E) (i j : Fin p),
      i ≠ j → v i = v j → T (Fin.append v w) = 0) :
    E [⋀^Fin p]→L[𝕜] E [⋀^Fin q]→L[𝕜] F := by
  let C := (T.domDomCongr finSumFinEquiv.symm).currySum
  let B := alternatizationCLM.compContinuousMultilinearMap C
  exact
    { B with
      map_eq_zero_of_eq' := by
        intro v i j hv hij
        change alternatizationCLM (C v) = 0
        have hz : C v = 0 := by
          ext w
          rw [show C v w = T (Fin.append v w) from
            currySum_domDomCongr_finSumFinEquiv_apply p q T v w]
          change T (Fin.append v w) = 0
          exact hleft v w i j hij hv
        rw [hz, _root_.map_zero] }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousMultilinearMap.toBlockAlternating then
    throwError "Refusing to shadow existing declaration ContinuousMultilinearMap.toBlockAlternating"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousMultilinearMap.toBlockAlternating ``Submission.ContinuousMultilinearMap.toBlockAlternating

open _root_.ContinuousMultilinearMap in
theorem toBlockAlternating_apply (p q : ℕ)
    (T : ContinuousMultilinearMap 𝕜 (fun _ : Fin (p + q) => E) F)
    (hleft : ∀ (v : Fin p → E) (w : Fin q → E) (i j : Fin p),
      i ≠ j → v i = v j → T (Fin.append v w) = 0)
    (hright : ∀ (v : Fin p → E) (w : Fin q → E) (i j : Fin q),
      i ≠ j → w i = w j → T (Fin.append v w) = 0)
    (v : Fin p → E) (w : Fin q → E) :
    toBlockAlternating p q T hleft v w = T (Fin.append v w) := by
  let C := (T.domDomCongr finSumFinEquiv.symm).currySum
  let A : E [⋀^Fin q]→L[𝕜] F :=
    { C v with
      map_eq_zero_of_eq' := by
        intro u i j hu hij
        change C v u = 0
        rw [currySum_domDomCongr_finSumFinEquiv_apply]
        exact hright v u i j hij hu }
  change alternatizationCLM A.toContinuousMultilinearMap w = _
  rw [alternatizationCLM_apply_toContinuousMultilinearMap]
  exact currySum_domDomCongr_finSumFinEquiv_apply p q T v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousMultilinearMap.toBlockAlternating_apply then
    throwError "Refusing to shadow existing declaration ContinuousMultilinearMap.toBlockAlternating_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousMultilinearMap.toBlockAlternating_apply ``Submission.ContinuousMultilinearMap.toBlockAlternating_apply

end

end ContinuousMultilinearMap
