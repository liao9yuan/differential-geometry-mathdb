/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.LocalDegree.InjectiveUnit
import Mathlib.Data.ZMod.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.LocalDegree

variable {d : ℕ}
  {f : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
  {U A : Set (EuclideanSpace ℝ (Fin (d + 1)))}

theorem euclideanLocalDegree_sub_eq_of_isPreconnected
    (hU : IsOpen U) (hf : ContinuousOn f U) (hinj : _root_.Set.InjOn f U)
    (hA : IsPreconnected A) (hAU : A ⊆ U)
    {x y : EuclideanSpace ℝ (Fin (d + 1))} (hx : x ∈ A) (hy : y ∈ A) :
    euclideanLocalDegree (fun z => f z - f x) x
        (isolatedZero_sub_of_injOn hU hf hinj (hAU hx)) =
      euclideanLocalDegree (fun z => f z - f y) y
        (isolatedZero_sub_of_injOn hU hf hinj (hAU hy)) := by
  let _ : PreconnectedSpace A := Subtype.preconnectedSpace hA
  let j : A → U := fun z => ⟨z, hAU z.2⟩
  have hj : Continuous j := continuous_subtype_val.subtype_mk _
  have hD := (isLocallyConstant_euclideanLocalDegree_sub_of_injOn hU hf hinj).comp_continuous hj
  exact hD.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨y, hy⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanLocalDegree_sub_eq_of_isPreconnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanLocalDegree_sub_eq_of_isPreconnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanLocalDegree_sub_eq_of_isPreconnected ``Submission.DifferentialGeometry.LocalDegree.euclideanLocalDegree_sub_eq_of_isPreconnected

theorem exists_euclideanLocalDegree_sign_of_isConnected
    (hU : IsOpen U) (hf : ContinuousOn f U) (hinj : _root_.Set.InjOn f U)
    (hA : IsConnected A) (hAU : A ⊆ U) :
    ∃ s : ZMod 2, ∀ x (hx : x ∈ A),
      euclideanLocalDegree (fun z => f z - f x) x
        (isolatedZero_sub_of_injOn hU hf hinj (hAU hx)) =
          if s = 0 then 1 else -1 := by
  obtain ⟨x₀, hx₀⟩ := hA.nonempty
  have hconst (x) (hx : x ∈ A) :=
    euclideanLocalDegree_sub_eq_of_isPreconnected hU hf hinj hA.isPreconnected hAU hx hx₀
  rcases euclideanLocalDegree_eq_one_or_neg_one_of_injOn hU hf hinj (hAU hx₀) with hp | hn
  · exact ⟨0, fun x hx => by simpa using (hconst x hx).trans hp⟩
  · refine ⟨1, fun x hx => ?_⟩
    simpa using (hconst x hx).trans hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.exists_euclideanLocalDegree_sign_of_isConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.exists_euclideanLocalDegree_sign_of_isConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.exists_euclideanLocalDegree_sign_of_isConnected ``Submission.DifferentialGeometry.LocalDegree.exists_euclideanLocalDegree_sign_of_isConnected

end DifferentialGeometry.LocalDegree
