import Submission.DifferentialGeometry.Topology.Handle.HalfBallCylinderCollar
import Submission.DifferentialGeometry.Topology.SphereSeparation.FlatCapCylinderSides

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Metric
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Topology.SphereSeparation.TwoSidedSeparation

theorem exists_flat_cap_collar
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set F} (d : TwoSidedSeparation S) (Ψ : (E × ℝ) ≃ₘ[ℝ] F)
    {R b σ : ℝ} (hR : 1 < R) (hb : 0 < b) (hσ : σ ≠ 0)
    (hS : ∀ p ∈ _root_.Metric.ball (0 : E) R ×ˢ _root_.Set.Ioo (-b) b,
      Ψ p ∈ S ↔ (‖p.1‖ ≤ 1 ∧ p.2 = 0) ∨ (‖p.1‖ = 1 ∧ 0 < σ * p.2)) :
    ∃ c : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, F) (E × ℝ) F ∞,
      _root_.Metric.closedBall (0 : E) 1 ×ˢ {(0 : ℝ)} ⊆ c.source ∧
      c.source ⊆ {p | |p.2| < 1 / 4} ∧
      c.target ⊆ Ψ '' (_root_.Metric.ball (0 : E) R ×ˢ _root_.Set.Ioo (-b) b) ∧
      (∀ p, c p = Ψ ((EuclideanGeometry.halfBallCylinderMap p).1, σ⁻¹ * p.2)) ∧
      (∀ x, c (x, 0) = Ψ (x, 0)) ∧
      (c.toOpenPartialHomeomorph.IsImage
        {p : E × ℝ | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1 ∧ 0 ≤ p.2} (closure d.positiveSide) ∨
        c.toOpenPartialHomeomorph.IsImage
          {p : E × ℝ | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1 ∧ 0 ≤ p.2} (closure d.negativeSide)) := by
  let J := ((ContinuousLinearEquiv.refl ℝ E).prodCongr
    (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 σ hσ)⁻¹)).toDiffeomorph
  have hJ (p : E × ℝ) : J p = (p.1, σ⁻¹ * p.2) := by
    change (p.1, p.2 * ↑((Units.mk0 σ hσ)⁻¹)) = _
    simp only [Units.val_inv_eq_inv_val, Units.val_mk0, mul_comm]
  obtain ⟨C, hKC, hCs, hCF, _⟩ := PartialDiffeomorph.exists_halfBall_cylinder_collar (E := E)
  let U := _root_.Metric.ball (0 : E) R ×ˢ _root_.Set.Ioo (-b) b
  let V := (J ∘ EuclideanGeometry.halfBallCylinderMap) ⁻¹' U
  have hV : IsOpen V := (isOpen_ball.prod isOpen_Ioo).preimage
    (J.continuous.comp EuclideanGeometry.contDiff_halfBallCylinderMap.continuous)
  let c := (DifferentialGeometry.Topology.PartialDiffeomorph.restrict C V hV).trans
    (J.trans Ψ).toPartialDiffeomorph
  have hcp (p : E × ℝ) : c p = Ψ ((EuclideanGeometry.halfBallCylinderMap p).1, σ⁻¹ * p.2) := by
    change Ψ (J (C p)) = _
    rw [congrFun hCF, hJ]
    rfl
  have hfix (x : E) : c (x, 0) = Ψ (x, 0) := by
    rw [hcp, EuclideanGeometry.halfBallCylinderMap_apply_zero, _root_.MulZeroClass.mul_zero]
  have hphysical (p : E × ℝ) (hp : p ∈ c.source) :
      ((EuclideanGeometry.halfBallCylinderMap p).1, σ⁻¹ * p.2) ∈ U := by
    have hpV : J (EuclideanGeometry.halfBallCylinderMap p) ∈ U := hp.1.2
    rwa [hJ] at hpV
  refine ⟨c, ?_, fun _ hp => hCs hp.1.1, ?_, hcp, hfix, ?_⟩
  · intro p hp
    refine ⟨⟨hKC hp, ?_⟩, _root_.Set.mem_univ _⟩
    change J (EuclideanGeometry.halfBallCylinderMap p) ∈ U
    have ht : p.2 = 0 := hp.2
    have he : p = (p.1, 0) := Prod.ext rfl ht
    rw [he, EuclideanGeometry.halfBallCylinderMap_apply_zero, hJ, _root_.MulZeroClass.mul_zero]
    exact ⟨closedBall_subset_ball hR hp.1,
      by change -b < 0 ∧ 0 < b; exact ⟨neg_neg_of_pos hb, hb⟩⟩
  · intro y hy
    refine ⟨((EuclideanGeometry.halfBallCylinderMap (c.symm y)).1, σ⁻¹ * (c.symm y).2),
      hphysical _ (c.map_target hy), ?_⟩
    rw [← hcp]
    exact c.right_inv hy
  · have himage (A : Set F)
        (hside : ∀ p ∈ U, Ψ p ∈ A ↔ ‖p.1‖ ≤ 1 ∧ 0 ≤ σ * p.2) :
        c.toOpenPartialHomeomorph.IsImage
          {p : E × ℝ | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1 ∧ 0 ≤ p.2} A := by
      intro p hp
      change c p ∈ A ↔ _
      rw [hcp, hside _ (hphysical p hp)]
      simp only [mul_inv_cancel_left₀ hσ]
      have hn : ‖(EuclideanGeometry.halfBallCylinderMap p).1‖ ≤ 1 ↔
          ‖(EuclideanGeometry.halfBallCylinderMap p).1‖ ^ 2 ≤ 1 := by
        constructor <;> intro h <;> nlinarith [norm_nonneg (EuclideanGeometry.halfBallCylinderMap p).1]
      rw [hn]
      exact EuclideanGeometry.halfBallCylinderMap_mem_cylinder_iff (hCs hp.1.1)
    rcases d.closed_sides_in_flat_cap_cylinder Ψ.toHomeomorph zero_lt_one hR hb hσ hS with
      ⟨hpos, _⟩ | ⟨_, hneg⟩
    · exact Or.inl (himage _ hpos)
    · exact Or.inr (himage _ hneg)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.TwoSidedSeparation.exists_flat_cap_collar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.TwoSidedSeparation.exists_flat_cap_collar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.TwoSidedSeparation.exists_flat_cap_collar ``Submission.DifferentialGeometry.Topology.SphereSeparation.TwoSidedSeparation.exists_flat_cap_collar

end DifferentialGeometry.Topology.SphereSeparation.TwoSidedSeparation
