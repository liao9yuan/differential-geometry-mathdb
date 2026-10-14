/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.LocalDegree.BoundaryHomotopy
import Submission.DifferentialGeometry.Topology.LocalDegree.Product.Negative
import Submission.DifferentialGeometry.Topology.LocalDegree.EmbeddingParity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Metric
open scoped _root_.unitInterval

namespace DifferentialGeometry.LocalDegree

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (d + 1))

theorem euclideanLocalDegree_eq_of_same_sides_and_trace
    {f g : E → E} {R : ℝ}
    (hf : IsolatingRadius f 0 R) (hg : IsolatingRadius g 0 R)
    (ℓ m : E →ₗ[ℝ] ℝ)
    (htrace : ∀ y ∈ _root_.Metric.sphere 0 R, ℓ y = 0 → f y = g y)
    (hpos : ∀ y ∈ _root_.Metric.sphere 0 R, 0 < ℓ y → 0 < m (f y) ∧ 0 < m (g y))
    (hneg : ∀ y ∈ _root_.Metric.sphere 0 R, ℓ y < 0 → m (f y) < 0 ∧ m (g y) < 0) :
    euclideanLocalDegree f 0 ⟨R, hf⟩ = euclideanLocalDegree g 0 ⟨R, hg⟩ := by
  let H : I × E → E := fun p => (1 - (p.1 : ℝ)) • f p.2 + (p.1 : ℝ) • g p.2
  have hH : ContinuousOn H (_root_.Set.univ ×ˢ _root_.Metric.sphere 0 R) := by
    have hfc : ContinuousOn (fun p : I × E => f p.2) (_root_.Set.univ ×ˢ _root_.Metric.sphere 0 R) :=
      hf.continuousOn.comp continuous_snd.continuousOn
        (fun p hp => _root_.Metric.sphere_subset_closedBall hp.2)
    have hgc : ContinuousOn (fun p : I × E => g p.2) (_root_.Set.univ ×ˢ _root_.Metric.sphere 0 R) :=
      hg.continuousOn.comp continuous_snd.continuousOn
        (fun p hp => _root_.Metric.sphere_subset_closedBall hp.2)
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).continuousOn.smul
      hfc).add ((continuous_subtype_val.comp continuous_fst).continuousOn.smul hgc)
  have hn : ∀ t y, y ∈ _root_.Metric.sphere 0 R → H (t, y) ≠ 0 := by
    intro t y hy hzero
    have ht0 := t.2.1
    have ht1 := t.2.2
    have heq := congrArg m hzero
    change m ((1 - (t : ℝ)) • f y + (t : ℝ) • g y) = m 0 at heq
    rw [map_add, map_smul, map_smul, map_zero] at heq
    change (1 - (t : ℝ)) * m (f y) + (t : ℝ) * m (g y) = 0 at heq
    rcases lt_trichotomy (ℓ y) 0 with hlt | he | hgt
    · obtain ⟨hfneg, hgneg⟩ := hneg y hy hlt
      nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht1) hfneg.le,
        mul_nonpos_of_nonneg_of_nonpos ht0 hgneg.le]
    · have hfg := htrace y hy he
      have hyne : y ≠ 0 := by
        intro hy0
        have hnorm := mem_sphere_zero_iff_norm.mp hy
        rw [hy0, norm_zero] at hnorm
        linarith [hf.pos]
      apply hg.nonzero y (_root_.Metric.sphere_subset_closedBall hy) hyne
      change (1 - (t : ℝ)) • f y + (t : ℝ) • g y = 0 at hzero
      rw [hfg, ← add_smul, sub_add_cancel, one_smul] at hzero
      exact hzero
    · obtain ⟨hfpos, hgpos⟩ := hpos y hy hgt
      nlinarith [mul_nonneg (sub_nonneg.mpr ht1) hfpos.le, mul_nonneg ht0 hgpos.le]
  exact euclideanLocalDegree_eq_of_boundaryHomotopy hf hg H hH hn
    (fun y _ => by simp [H]) (fun y _ => by simp [H])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanLocalDegree_eq_of_same_sides_and_trace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanLocalDegree_eq_of_same_sides_and_trace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanLocalDegree_eq_of_same_sides_and_trace ``Submission.DifferentialGeometry.LocalDegree.euclideanLocalDegree_eq_of_same_sides_and_trace

private theorem productField_coordinates
    (f : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)))
    (y : EuclideanSpace ℝ (Fin ((d + 1) + 1))) :
    euclideanProductField f y = (euclideanProductChart d).symm
      (f (euclideanProductChart d y).1, (euclideanProductChart d y).2) := by
  have h := euclideanProductChart_field f (euclideanProductChart d y)
  rw [(euclideanProductChart d).symm_apply_apply] at h
  exact (euclideanProductChart d).toEquiv.eq_symm_apply.mpr h

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.productField_coordinates
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.productField_coordinates target :: scope.openDecls } }

private theorem negativeProductField_coordinates
    (f : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)))
    (y : EuclideanSpace ℝ (Fin ((d + 1) + 1))) :
    euclideanNegativeProductField f y = (euclideanProductChart d).symm
      (f (euclideanProductChart d y).1, -(euclideanProductChart d y).2) := by
  have h := euclideanNegativeProductField_point f
    (euclideanProductChart d y).1 (euclideanProductChart d y).2
  change euclideanNegativeProductField f
    ((euclideanProductChart d).symm (euclideanProductChart d y)) = _ at h
  rwa [(euclideanProductChart d).symm_apply_apply] at h

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.negativeProductField_coordinates
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.negativeProductField_coordinates target :: scope.openDecls } }

theorem euclideanLocalDegree_eq_of_preserves_normal_sides
    {f : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {F : EuclideanSpace ℝ (Fin ((d + 1) + 1)) → EuclideanSpace ℝ (Fin ((d + 1) + 1))}
    {R : ℝ} (hf : IsolatingRadius f 0 R) (hF : IsolatingRadius F 0 R)
    (htrace : ∀ y ∈ _root_.Metric.sphere 0 R, (euclideanProductChart d y).2 = 0 →
      F y = euclideanProductPoint d (f (euclideanProductChart d y).1) 0)
    (hpos : ∀ y ∈ _root_.Metric.sphere 0 R, 0 < (euclideanProductChart d y).2 →
      0 < (euclideanProductChart d (F y)).2)
    (hneg : ∀ y ∈ _root_.Metric.sphere 0 R, (euclideanProductChart d y).2 < 0 →
      (euclideanProductChart d (F y)).2 < 0) :
    euclideanLocalDegree F 0 ⟨R, hF⟩ = euclideanLocalDegree f 0 ⟨R, hf⟩ := by
  let ℓ := (LinearMap.snd ℝ (EuclideanSpace ℝ (Fin (d + 1))) ℝ).comp
    (euclideanProductChart d).toLinearMap
  have hheight (y) : ℓ (euclideanProductField f y) = ℓ y := by
    change (euclideanProductChart d (euclideanProductField f y)).2 = _
    rw [productField_coordinates, (euclideanProductChart d).apply_symm_apply]
    rfl
  have h := euclideanLocalDegree_eq_of_same_sides_and_trace hF hf.euclideanProduct ℓ ℓ
    (fun y hy hy0 => by
      rw [htrace y hy hy0, productField_coordinates, show (euclideanProductChart d y).2 = 0
        from hy0]
      rfl)
    (fun y hy hyp => ⟨hpos y hy hyp, by rw [hheight]; exact hyp⟩)
    (fun y hy hyn => ⟨hneg y hy hyn, by rw [hheight]; exact hyn⟩)
  exact h.trans (euclideanLocalDegree_product_zero ⟨R, hf⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanLocalDegree_eq_of_preserves_normal_sides then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanLocalDegree_eq_of_preserves_normal_sides"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanLocalDegree_eq_of_preserves_normal_sides ``Submission.DifferentialGeometry.LocalDegree.euclideanLocalDegree_eq_of_preserves_normal_sides

theorem euclideanLocalDegree_eq_neg_of_reverses_normal_sides
    {f : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {F : EuclideanSpace ℝ (Fin ((d + 1) + 1)) → EuclideanSpace ℝ (Fin ((d + 1) + 1))}
    {R : ℝ} (hf : IsolatingRadius f 0 R) (hF : IsolatingRadius F 0 R)
    (htrace : ∀ y ∈ _root_.Metric.sphere 0 R, (euclideanProductChart d y).2 = 0 →
      F y = euclideanProductPoint d (f (euclideanProductChart d y).1) 0)
    (hpos : ∀ y ∈ _root_.Metric.sphere 0 R, 0 < (euclideanProductChart d y).2 →
      (euclideanProductChart d (F y)).2 < 0)
    (hneg : ∀ y ∈ _root_.Metric.sphere 0 R, (euclideanProductChart d y).2 < 0 →
      0 < (euclideanProductChart d (F y)).2) :
    euclideanLocalDegree F 0 ⟨R, hF⟩ = -euclideanLocalDegree f 0 ⟨R, hf⟩ := by
  let ℓ := (LinearMap.snd ℝ (EuclideanSpace ℝ (Fin (d + 1))) ℝ).comp
    (euclideanProductChart d).toLinearMap
  have hheight (y) : (-ℓ) (euclideanNegativeProductField f y) = ℓ y := by
    change -(euclideanProductChart d (euclideanNegativeProductField f y)).2 = _
    rw [negativeProductField_coordinates, (euclideanProductChart d).apply_symm_apply, neg_neg]
    rfl
  have h := euclideanLocalDegree_eq_of_same_sides_and_trace
    hF hf.euclideanProduct.euclideanNegativeProduct ℓ (-ℓ)
    (fun y hy hy0 => by
      rw [htrace y hy hy0, negativeProductField_coordinates,
        show (euclideanProductChart d y).2 = 0 from hy0, neg_zero]
      rfl)
    (fun y hy hyp => ⟨neg_pos.mpr (hpos y hy hyp), by rw [hheight]; exact hyp⟩)
    (fun y hy hyn => ⟨neg_neg_of_pos (hneg y hy hyn), by rw [hheight]; exact hyn⟩)
  have hz : euclideanProductPoint d 0 0 = 0 := by simp [euclideanProductPoint]
  have hdegree := euclideanLocalDegree_negativeProduct (d := d) (⟨R, hf⟩ : isolatedZero f 0)
  apply h.trans
  simpa only [hz] using hdegree

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanLocalDegree_eq_neg_of_reverses_normal_sides then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanLocalDegree_eq_neg_of_reverses_normal_sides"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanLocalDegree_eq_neg_of_reverses_normal_sides ``Submission.DifferentialGeometry.LocalDegree.euclideanLocalDegree_eq_neg_of_reverses_normal_sides
theorem embeddingOrientationParity_eq_of_preserves_normal_sides
    {f : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {F : EuclideanSpace ℝ (Fin ((d + 1) + 1)) → EuclideanSpace ℝ (Fin ((d + 1) + 1))}
    {R : ℝ} (hf : IsolatingRadius f 0 R) (hF : IsolatingRadius F 0 R)
    (hfi : _root_.Set.InjOn f (_root_.Metric.ball 0 R)) (hFi : _root_.Set.InjOn F (_root_.Metric.ball 0 R))
    (htrace : ∀ y ∈ _root_.Metric.sphere 0 R, (euclideanProductChart d y).2 = 0 →
      F y = euclideanProductPoint d (f (euclideanProductChart d y).1) 0)
    (hpos : ∀ y ∈ _root_.Metric.sphere 0 R, 0 < (euclideanProductChart d y).2 →
      0 < (euclideanProductChart d (F y)).2)
    (hneg : ∀ y ∈ _root_.Metric.sphere 0 R, (euclideanProductChart d y).2 < 0 →
      (euclideanProductChart d (F y)).2 < 0) :
    embeddingOrientationParity _root_.Metric.isOpen_ball (hF.continuousOn.mono _root_.Metric.ball_subset_closedBall)
        hFi ⟨0, _root_.Metric.mem_ball_self hF.pos⟩ =
      embeddingOrientationParity _root_.Metric.isOpen_ball (hf.continuousOn.mono _root_.Metric.ball_subset_closedBall)
        hfi ⟨0, _root_.Metric.mem_ball_self hf.pos⟩ := by
  have hdegree := euclideanLocalDegree_eq_of_preserves_normal_sides hf hF htrace hpos hneg
  unfold embeddingOrientationParity
  simp only [hf.zero, hF.zero, sub_zero]
  rw [hdegree]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.embeddingOrientationParity_eq_of_preserves_normal_sides then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.embeddingOrientationParity_eq_of_preserves_normal_sides"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.embeddingOrientationParity_eq_of_preserves_normal_sides ``Submission.DifferentialGeometry.LocalDegree.embeddingOrientationParity_eq_of_preserves_normal_sides

theorem embeddingOrientationParity_eq_add_one_of_reverses_normal_sides
    {f : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {F : EuclideanSpace ℝ (Fin ((d + 1) + 1)) → EuclideanSpace ℝ (Fin ((d + 1) + 1))}
    {R : ℝ} (hf : IsolatingRadius f 0 R) (hF : IsolatingRadius F 0 R)
    (hfi : _root_.Set.InjOn f (_root_.Metric.ball 0 R)) (hFi : _root_.Set.InjOn F (_root_.Metric.ball 0 R))
    (htrace : ∀ y ∈ _root_.Metric.sphere 0 R, (euclideanProductChart d y).2 = 0 →
      F y = euclideanProductPoint d (f (euclideanProductChart d y).1) 0)
    (hpos : ∀ y ∈ _root_.Metric.sphere 0 R, 0 < (euclideanProductChart d y).2 →
      (euclideanProductChart d (F y)).2 < 0)
    (hneg : ∀ y ∈ _root_.Metric.sphere 0 R, (euclideanProductChart d y).2 < 0 →
      0 < (euclideanProductChart d (F y)).2) :
    embeddingOrientationParity _root_.Metric.isOpen_ball (hF.continuousOn.mono _root_.Metric.ball_subset_closedBall)
        hFi ⟨0, _root_.Metric.mem_ball_self hF.pos⟩ =
      embeddingOrientationParity _root_.Metric.isOpen_ball (hf.continuousOn.mono _root_.Metric.ball_subset_closedBall)
        hfi ⟨0, _root_.Metric.mem_ball_self hf.pos⟩ + 1 := by
  have hdegree := euclideanLocalDegree_eq_neg_of_reverses_normal_sides hf hF htrace hpos hneg
  have hunit := euclideanLocalDegree_isUnit_of_isolatingRadius_injOn hf hfi
  unfold embeddingOrientationParity
  simp only [hf.zero, hF.zero, sub_zero]
  rw [hdegree]
  rcases Int.isUnit_iff.mp hunit with hp | hn
  · simp [hp]
  · simp [hn, show (1 : ZMod 2) + 1 = 0 from by decide]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.embeddingOrientationParity_eq_add_one_of_reverses_normal_sides then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.embeddingOrientationParity_eq_add_one_of_reverses_normal_sides"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.embeddingOrientationParity_eq_add_one_of_reverses_normal_sides ``Submission.DifferentialGeometry.LocalDegree.embeddingOrientationParity_eq_add_one_of_reverses_normal_sides
end DifferentialGeometry.LocalDegree
