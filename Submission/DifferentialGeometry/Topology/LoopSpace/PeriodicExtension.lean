import Mathlib.Algebra.AddConstMap.Basic
import Mathlib.Topology.Instances.AddCircle.Real

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set

namespace AddConstMap
open _root_.AddConstMap

open _root_.AddConstMap in
theorem exists_continuous_extension_Icc {f : ℝ → ℝ} (a : ℝ)
    (hf : ContinuousOn f (_root_.Set.Icc a (a + 1))) (hp : f (a + 1) = f a + 1) :
    ∃ g : AddConstMap ℝ ℝ 1 1, Continuous g ∧ _root_.Set.EqOn g f (_root_.Set.Icc a (a + 1)) := by
  let D := AddCircle.liftIco (1 : ℝ) a (fun x => f x - x)
  have hD : Continuous D := AddCircle.liftIco_continuous
    (by rw [hp]; ring) (hf.sub continuousOn_id)
  let g : AddConstMap ℝ ℝ 1 1 :=
    ⟨fun x => x + D (x : AddCircle (1 : ℝ)), fun x => by
      rw [AddCircle.coe_add_period]
      ring⟩
  have hgc : Continuous g := continuous_id.add (hD.comp (AddCircle.continuous_mk' (1 : ℝ)))
  have hco : _root_.Set.EqOn g f (_root_.Set.Ico a (a + 1)) := by
    intro x hx
    change x + AddCircle.liftIco (1 : ℝ) a (fun x => f x - x) (x : AddCircle (1 : ℝ)) = f x
    rw [AddCircle.liftIco_coe_apply hx]
    ring
  refine ⟨g, hgc, ?_⟩
  intro x hx
  rcases lt_or_eq_of_le hx.2 with hxlt | rfl
  · exact hco ⟨hx.1, hxlt⟩
  · have hg : g (a + 1) = g a + 1 := g.map_add_const' a
    rw [hg, hco (show a ∈ _root_.Set.Ico a (a + 1) from ⟨le_rfl, by linarith⟩), hp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddConstMap.exists_continuous_extension_Icc then
    throwError "Refusing to shadow existing declaration AddConstMap.exists_continuous_extension_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `AddConstMap.exists_continuous_extension_Icc ``Submission.AddConstMap.exists_continuous_extension_Icc

end AddConstMap

end
