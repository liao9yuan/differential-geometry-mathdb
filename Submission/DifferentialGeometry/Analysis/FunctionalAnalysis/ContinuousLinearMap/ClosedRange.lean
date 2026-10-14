import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Prod

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace ContinuousLinearMap
open _root_.ContinuousLinearMap

variable {𝕜 X Y Z W : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]

open _root_.ContinuousLinearMap in
private theorem isClosed_range_prod_of_lifting
    (J : X →L[𝕜] Y) (QH : X →L[𝕜] Z)
    (QL : Y →L[𝕜] W) (K : Z →L[𝕜] W)
    (hcomm : QL.comp J = K.comp QH)
    (hlift : ∀ y z, QL y = K z → ∃ x, J x = y ∧ QH x = z) :
    IsClosed (Set.range (J.prod QH)) := by
  have hrange : Set.range (J.prod QH) = {p : Y × Z | QL p.1 = K p.2} := by
    ext p
    constructor
    · rintro ⟨x, rfl⟩
      exact DFunLike.congr_fun hcomm x
    · intro hp
      obtain ⟨x, hJx, hQx⟩ := hlift p.1 p.2 hp
      exact ⟨x, Prod.ext hJx hQx⟩
  rw [hrange]
  exact isClosed_eq (QL.continuous.comp continuous_fst) (K.continuous.comp continuous_snd)

run_cmd do
  let target := ``Submission.ContinuousLinearMap.isClosed_range_prod_of_lifting
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `ContinuousLinearMap.isClosed_range_prod_of_lifting target :: scope.openDecls } }

open _root_.ContinuousLinearMap in
theorem exists_norm_le_max_of_lifting
    [CompleteSpace X] [CompleteSpace Y] [CompleteSpace Z]
    (J : X →L[𝕜] Y) (QH : X →L[𝕜] Z)
    (QL : Y →L[𝕜] W) (K : Z →L[𝕜] W)
    (hJ : Function.Injective J)
    (hcomm : QL.comp J = K.comp QH)
    (hlift : ∀ y z, QL y = K z → ∃ x, J x = y ∧ QH x = z) :
    ∃ C ≥ (0 : ℝ), ∀ x, ‖x‖ ≤ C * _root_.Max.max ‖J x‖ ‖QH x‖ := by
  have hprod : Function.Injective (J.prod QH) := by
    intro x y hxy
    exact hJ (congrArg Prod.fst hxy)
  obtain ⟨C, hC⟩ := (J.prod QH).antilipschitz_of_injective_of_isClosed_range
    hprod (isClosed_range_prod_of_lifting J QH QL K hcomm hlift)
  refine ⟨C, C.coe_nonneg, fun x => ?_⟩
  simpa only [map_zero, dist_zero_right, _root_.ContinuousLinearMap.prod_apply, Prod.norm_def] using hC.le_mul_dist x 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousLinearMap.exists_norm_le_max_of_lifting then
    throwError "Refusing to shadow existing declaration ContinuousLinearMap.exists_norm_le_max_of_lifting"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousLinearMap.exists_norm_le_max_of_lifting ``Submission.ContinuousLinearMap.exists_norm_le_max_of_lifting

end ContinuousLinearMap
