import Mathlib.Analysis.Calculus.FDeriv.Extend

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.Set
open scoped _root_.Topology

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasDerivAt_of_punct {f g : ℝ → E} {x : ℝ}
    (h : ∀ᶠ y in 𝓝[≠] x, HasDerivAt f (g y) y) (hf : ContinuousAt f x)
    (hg : ContinuousAt g x) : HasDerivAt f (g x) x := by
  have hGT : ∀ᶠ y in 𝓝[>] x, HasDerivAt f (g y) y :=
    h.filter_mono (nhdsGT_le_nhdsNE x)
  have hLT : ∀ᶠ y in 𝓝[<] x, HasDerivAt f (g y) y :=
    h.filter_mono (nhdsLT_le_nhdsNE x)
  have hgGT : _root_.Filter.Tendsto g (𝓝[>] x) (𝓝 (g x)) := _root_.Filter.tendsto_inf_left hg
  have hgLT : _root_.Filter.Tendsto g (𝓝[<] x) (𝓝 (g x)) := _root_.Filter.tendsto_inf_left hg
  have hright : HasDerivWithinAt f (g x) (_root_.Set.Ici x) x := by
    apply hasDerivWithinAt_Ici_of_tendsto_deriv
      (s := {y | HasDerivAt f (g y) y})
    · intro y hy
      exact hy.differentiableAt.differentiableWithinAt
    · exact hf.continuousWithinAt
    · exact hGT
    · exact hgGT.congr' (hGT.mono fun _ hy => hy.deriv.symm)
  have hleft : HasDerivWithinAt f (g x) (_root_.Set.Iic x) x := by
    apply hasDerivWithinAt_Iic_of_tendsto_deriv
      (s := {y | HasDerivAt f (g y) y})
    · intro y hy
      exact hy.differentiableAt.differentiableWithinAt
    · exact hf.continuousWithinAt
    · exact hLT
    · exact hgLT.congr' (hLT.mono fun _ hy => hy.deriv.symm)
  have hfull := hleft.union hright
  rw [_root_.Set.Iic_union_Ici] at hfull
  exact hfull.hasDerivAt _root_.Filter.univ_mem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.hasDerivAt_of_punct then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.hasDerivAt_of_punct"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.hasDerivAt_of_punct ``Submission.DifferentialGeometry.hasDerivAt_of_punct

end DifferentialGeometry
