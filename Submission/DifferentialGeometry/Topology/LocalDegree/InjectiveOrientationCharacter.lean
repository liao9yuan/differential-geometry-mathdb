/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.LocalDegree.InjectiveDeterminantSign

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Metric _root_.Set _root_.Filter
open scoped _root_.Topology

namespace DifferentialGeometry.LocalDegree

variable {d : ℕ}

theorem isLocallyConstant_euclideanLocalDegree_sub_of_injOn
    {f : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {U : Set (EuclideanSpace ℝ (Fin (d + 1)))}
    (hU : IsOpen U) (hf : ContinuousOn f U) (hinj : _root_.Set.InjOn f U) :
    IsLocallyConstant (fun z : U =>
      euclideanLocalDegree (fun w => f w - f z) z
        (isolatedZero_sub_of_injOn hU hf hinj z.2)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro z
  obtain ⟨R, hR, hRU⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds z.2)
  have hR2 : 0 < R / 2 := half_pos hR
  have hsub : _root_.Metric.closedBall (z : EuclideanSpace ℝ (Fin (d + 1))) (2 * (R / 2)) ⊆ U := by
    rw [mul_div_cancel₀ R two_ne_zero]
    exact hRU
  have hball : ∀ᶠ w : U in 𝓝 z,
      (w : EuclideanSpace ℝ (Fin (d + 1))) ∈
        ball (z : EuclideanSpace ℝ (Fin (d + 1))) (R / 2) :=
    (continuous_subtype_val.tendsto z).eventually (_root_.Metric.ball_mem_nhds _ hR2)
  filter_upwards [hball] with w hw
  exact (euclideanLocalDegree_sub_eq_of_mem_ball hf hinj hR2 hsub hw _ _).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.isLocallyConstant_euclideanLocalDegree_sub_of_injOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.isLocallyConstant_euclideanLocalDegree_sub_of_injOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.isLocallyConstant_euclideanLocalDegree_sub_of_injOn ``Submission.DifferentialGeometry.LocalDegree.isLocallyConstant_euclideanLocalDegree_sub_of_injOn

theorem euclideanLocalDegree_sub_eq_of_injOn
    {f : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {U : Set (EuclideanSpace ℝ (Fin (d + 1)))}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    (hf : ContinuousOn f U) (hinj : _root_.Set.InjOn f U)
    {x y : EuclideanSpace ℝ (Fin (d + 1))} (hx : x ∈ U) (hy : y ∈ U) :
    euclideanLocalDegree (fun z => f z - f x) x
        (isolatedZero_sub_of_injOn hU hf hinj hx) =
      euclideanLocalDegree (fun z => f z - f y) y
        (isolatedZero_sub_of_injOn hU hf hinj hy) := by
  have hpre : PreconnectedSpace U := Subtype.preconnectedSpace hUc
  have hD := isLocallyConstant_euclideanLocalDegree_sub_of_injOn hU hf hinj
  exact hD.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨y, hy⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanLocalDegree_sub_eq_of_injOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanLocalDegree_sub_eq_of_injOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanLocalDegree_sub_eq_of_injOn ``Submission.DifferentialGeometry.LocalDegree.euclideanLocalDegree_sub_eq_of_injOn

end DifferentialGeometry.LocalDegree
