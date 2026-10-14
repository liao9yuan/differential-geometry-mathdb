import Mathlib.Topology.Algebra.ConstMulAction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

run_cmd do
  let env ← Lean.getEnv
  for source in ([`ProperlyDiscontinuousSMul] : List Lean.Name) do
    if let some info := Mathlib.Tactic.ToAdditive.translations.find? env source then
      Mathlib.Tactic.ToAdditive.translations.add (`Submission ++ source)
        { info with translation := `Submission ++ info.translation }

set_option autoImplicit false

open _root_.Set

variable {Γ T : Type*} [TopologicalSpace T] [SMul Γ T]

open _root_.ProperlyDiscontinuousSMul in
@[to_additive]
theorem ProperlyDiscontinuousSMul.finite_of_isCompact_mapsTo
    [ProperlyDiscontinuousSMul Γ T] {K : Set T}
    (hK : IsCompact K) (hK_nonempty : K.Nonempty)
    (hK_mapsTo : ∀ γ : Γ, _root_.Set.MapsTo (γ • ·) K K) :
    Finite Γ := by
  apply Finite.of_finite_univ
  refine (_root_.ProperlyDiscontinuousSMul.finite_disjoint_inter_image hK hK).subset ?_
  intro γ _
  obtain ⟨x, hx⟩ := hK_nonempty
  exact ⟨γ • x, ⟨x, hx, rfl⟩, hK_mapsTo γ hx⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ProperlyDiscontinuousSMul
  let env ← Lean.getEnv
  if env.contains `ProperlyDiscontinuousSMul.finite_of_isCompact_mapsTo then
    throwError "Refusing to shadow existing declaration ProperlyDiscontinuousSMul.finite_of_isCompact_mapsTo"
  Lean.modifyEnv fun env => Lean.addAlias env `ProperlyDiscontinuousSMul.finite_of_isCompact_mapsTo ``Submission.ProperlyDiscontinuousSMul.finite_of_isCompact_mapsTo
run_cmd do
  let env ← Lean.getEnv
  if let some info := Mathlib.Tactic.ToAdditive.translations.find? env ``Submission.ProperlyDiscontinuousSMul.finite_of_isCompact_mapsTo then
    let target := info.translation
    if (`Submission).isPrefixOf target then
      let original := target.replacePrefix `Submission .anonymous
      if env.contains original then
        throwError "Refusing to shadow existing additive declaration {original}"
      Lean.modifyEnv fun env => Lean.addAlias env original target
      let mut parent := target.getPrefix
      while !parent.isAnonymous do
        Lean.modifyEnv fun env => env.registerNamespace parent
        parent := parent.getPrefix
