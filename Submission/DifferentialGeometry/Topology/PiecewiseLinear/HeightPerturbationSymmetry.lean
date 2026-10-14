/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.HeightPerturbation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_continuousLinearMap_injOn_preserving_strict_order_and_halfSpace_below_of_isPolyhedron
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A B : Set E} (hA : A.Finite) (hB : B.Finite)
    (ℓ m : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) {D : Set E} (hD : IsPolyhedron D) (p : E)
    (hlevel : ∀ x ∈ D, ℓ x = ℓ p) (hside : ∀ x ∈ D \ {p}, m p < m x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : E →L[ℝ] ℝ, _root_.Dist.dist f ℓ < ε ∧ f ≠ 0 ∧ _root_.Set.InjOn f A ∧
      (∀ x ∈ B, ∀ y ∈ B, ℓ x < ℓ y → f x < f y) ∧
      ∀ x ∈ D \ {p}, f x < f p := by
  have hℓNeg : -ℓ ≠ 0 := neg_ne_zero.mpr hℓ
  have hlevelNeg : ∀ x ∈ D, (-ℓ) x = (-ℓ) p := by
    intro x hx
    simpa only [neg_apply, neg_inj] using hlevel x hx
  obtain ⟨g, hgε, hgne, hginj, hgorder, hgside⟩ :=
    exists_continuousLinearMap_injOn_preserving_strict_order_and_halfSpace_of_isPolyhedron
      hA hB (-ℓ) m hℓNeg hD p hlevelNeg hside hε
  refine ⟨-g, ?_, neg_ne_zero.mpr hgne, ?_, ?_, ?_⟩
  · calc
      dist (-g) ℓ = _root_.Dist.dist (-g) (-(-ℓ)) := congrArg (_root_.Dist.dist (-g)) (neg_neg ℓ).symm
      _ = _root_.Dist.dist g (-ℓ) := dist_neg_neg g (-ℓ)
      _ < ε := hgε
  · intro x hx y hy hxy
    exact hginj hx hy (neg_injective hxy)
  · intro x hx y hy hxy
    have hneg : (-ℓ) y < (-ℓ) x := by
      simpa only [neg_apply, neg_lt_neg_iff] using hxy
    have hgyx := hgorder y hy x hx hneg
    simpa only [neg_apply, neg_lt_neg_iff] using hgyx
  · intro x hx
    have hgpx := hgside x hx
    simpa only [neg_apply, neg_lt_neg_iff] using hgpx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_continuousLinearMap_injOn_preserving_strict_order_and_halfSpace_below_of_isPolyhedron then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_continuousLinearMap_injOn_preserving_strict_order_and_halfSpace_below_of_isPolyhedron"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_continuousLinearMap_injOn_preserving_strict_order_and_halfSpace_below_of_isPolyhedron ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_continuousLinearMap_injOn_preserving_strict_order_and_halfSpace_below_of_isPolyhedron

end DifferentialGeometry.Topology.PiecewiseLinear
