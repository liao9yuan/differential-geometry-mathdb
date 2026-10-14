import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.Replacement.BoundaryCap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section

open _root_.Set _root_.Metric _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.NNReal _root_.ENNReal _root_.Topology

namespace DifferentialGeometry.Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem periodicLoopCone_mapsTo_closedBall (p : F) {a : ℝ → F}
    (ha : Function.Periodic a 1) {η : ℝ} (hbound : ∀ t, ‖a t - p‖ ≤ η) :
    MapsTo (periodicLoopCone p ha) (_root_.Metric.closedBall (0 : ℂ) 1) (_root_.Metric.closedBall p η) := by
  have hη : 0 ≤ η := (norm_nonneg (a 0 - p)).trans (hbound 0)
  have hcircle (z : Circle) : ‖periodicCircleMap ha z - p‖ ≤ η := by
    let ξ : loopCircle := (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm z +
      ((1 / 2 : ℝ) : loopCircle)
    obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective ξ
    change ‖ha.lift ξ - p‖ ≤ η
    rw [← ht, Function.Periodic.lift_coe]
    exact hbound t
  intro z hz
  rw [_root_.Metric.mem_closedBall, dist_eq_norm]
  change ‖(p + ‖z‖ • (periodicCircleMap ha (radialDirection z) - p)) - p‖ ≤ η
  rw [add_sub_cancel_left, norm_smul, norm_norm]
  have hz1 : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
  exact (mul_le_mul_of_nonneg_left (hcircle _) (norm_nonneg _)).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hz1 hη)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.periodicLoopCone_mapsTo_closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.periodicLoopCone_mapsTo_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.periodicLoopCone_mapsTo_closedBall ``Submission.DifferentialGeometry.Topology.periodicLoopCone_mapsTo_closedBall

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_boundary_cap_in_ball_of_short_lift_increment
    (Γ : ℝ → F) {KΓ J : ℝ≥0} (hΓ : LipschitzWith KΓ Γ)
    (hperiod : Function.Periodic Γ 1)
    (hInv : AntilipschitzWith J (hperiod.lift : loopCircle → F))
    (f : ℂ → F) {Kf : ℝ≥0} (hf : LipschitzWith Kf f)
    (ψ : CircleDeg1Lift) (hψ : Continuous ψ)
    (htrace : ∀ t : ℝ, f (circleMap 0 1 (2 * Real.pi * t)) = Γ (ψ t))
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hshort : ψ (1 - Real.arccos (ρ / 2) / Real.pi) -
      ψ (Real.arccos (ρ / 2) / Real.pi) ≤ 2 / 3) {η : ℝ}
    (hsmall : (1 + 2 * (KΓ : ℝ) * (J : ℝ)) * Real.sqrt
      (∫ s in _root_.Set.Icc (0 : ℝ) 1, ‖deriv (fun s => f (circleMap (-1) ρ
        (-Real.arccos (ρ / 2) + 2 * Real.arccos (ρ / 2) * s))) s‖ ^ 2) ≤ η) :
    let a₀ := Real.arccos (ρ / 2) / Real.pi
    let b₀ := 1 - a₀
    let a : ℝ → F := fun s => f (circleMap (-1) ρ
      (-Real.arccos (ρ / 2) + 2 * Real.arccos (ρ / 2) * s))
    let b : ℝ → F := fun s => Γ ((1 - s) * ψ a₀ + s * ψ b₀)
    ∃ (ψbar : CircleDeg1Lift) (h : ℂ ≃ₜ ℂ) (q : ℂ → F),
      Continuous ψbar ∧
      _root_.Set.EqOn ψbar ψ (⋃ k : ℤ, _root_.Set.Ioo (a₀ + k) (b₀ + k))ᶜ ∧
      (∀ s ∈ _root_.Set.Icc (0 : ℝ) 1,
        ψbar (a₀ + s * (b₀ - a₀)) = (1 - s) * ψ a₀ + s * ψ b₀) ∧
      h '' _root_.Metric.closedBall (0 : ℂ) 1 = boundaryLens ρ ∧
      (∀ t : ℝ, h (circleMap 0 1 (2 * Real.pi * t - Real.pi)) = lensBoundaryLoop ρ t) ∧
      q = periodicLoopCone (a 0) (joinedLoop_periodic a b) ∘ h.symm ∧
      (∃ Cq : ℝ≥0, LipschitzWith Cq q) ∧
      _root_.Set.MapsTo q (boundaryLens ρ) (_root_.Metric.closedBall (a 0) η) ∧
      _root_.Set.EqOn q f (_root_.Metric.closedBall (0 : ℂ) 1 ∩ _root_.Metric.sphere (-1) ρ) ∧
      (∀ t : ℝ, attachBoundaryCap f q ρ (circleMap 0 1 (2 * Real.pi * t)) = Γ (ψbar t)) ∧
      (∫ z in boundaryLens ρ,
        (‖fderiv ℝ q z 1‖ ^ 2 + ‖fderiv ℝ q z Complex.I‖ ^ 2) / 2) ≤
        2 * (144 * (16 * Real.pi + 1) * (18 * Real.pi ^ 2 + 1)) ^ 2 *
          ((Real.pi / 2) * (1 + 2 * (KΓ : ℝ) * (J : ℝ)) ^ 2 +
            (2 + 8 * (KΓ : ℝ) ^ 2 * (J : ℝ) ^ 2) / (8 * Real.pi)) *
          (∫ s in _root_.Set.Icc (0 : ℝ) 1, ‖deriv a s‖ ^ 2) := by
  intro a₀ b₀ a b
  obtain ⟨ψbar, h, q, hψbar, hsame, hline, himage, hboundary, hq, hqLip, _, hseam,
      hcapTrace, hqEnergy⟩ := exists_boundary_cap_of_short_lift_increment
    (K := _root_.Set.univ) (U := _root_.Metric.closedBall (a 0) η) Γ hΓ hperiod hInv (_root_.Set.subset_univ _) f hf
    (_root_.Set.mapsTo_univ _ _) ψ hψ htrace hρ hρ1 hshort (by simpa only [a, _root_.MulZeroClass.mul_zero, add_zero] using
      (Subset.rfl : _root_.Metric.closedBall (a 0) η ⊆ _root_.Metric.closedBall (a 0) η)) hsmall
    id differentiable_id (LT := 1) (fun _ => by
      rw [fderiv_id]
      exact ContinuousLinearMap.norm_id_le) (_root_.Set.mapsTo_univ _ _)
      (fun _ _ => rfl)
  have hqeq : q = periodicLoopCone (a 0) (joinedLoop_periodic a b) ∘ h.symm := by
    simpa only [Function.id_comp] using hq
  let α := Real.arccos (ρ / 2)
  have hα : 0 < α := Real.arccos_pos.mpr (by linarith)
  have hαhalf : α < Real.pi / 2 := Real.arccos_lt_pi_div_two.mpr (by linarith)
  have ha₀b₀ : a₀ ≤ b₀ := by
    have hh : α / Real.pi < 1 / 2 := (div_lt_iff₀ Real.pi_pos).mpr (by linarith)
    dsimp only [a₀, b₀]
    linarith
  have ha0 : a 0 = Γ (ψ b₀) := by
    change f (circleMap (-1) ρ (-α + 2 * α * 0)) = Γ (ψ b₀)
    rw [_root_.MulZeroClass.mul_zero, add_zero,
      circleMap_neg_one_neg_arccos (by linarith : -2 ≤ ρ) (by linarith : ρ ≤ 2)]
    have he : 2 * Real.pi - 2 * α = 2 * Real.pi * b₀ := by
      dsimp only [b₀, a₀, α]
      field_simp
    rw [he]
    exact htrace b₀
  have ha1 : a 1 = Γ (ψ a₀) := by
    change f (circleMap (-1) ρ (-α + 2 * α * 1)) = Γ (ψ a₀)
    rw [show -α + 2 * α * 1 = α by ring,
      circleMap_neg_one_arccos (by linarith : -2 ≤ ρ) (by linarith : ρ ≤ 2)]
    have he : 2 * α = 2 * Real.pi * a₀ := by
      dsimp only [a₀, α]
      field_simp
    rw [he]
    exact htrace a₀
  have haLip : LipschitzWith (Kf * (Real.nnabs ρ * Real.nnabs (2 * α))) a := by
    have hparam : LipschitzWith (Real.nnabs (2 * α)) (fun s : ℝ => -α + 2 * α * s) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simp only [Real.dist_eq, add_sub_add_left_eq_sub, ← mul_sub, abs_mul, Real.coe_nnabs]
      exact le_rfl
    exact hf.comp ((lipschitzWith_circleMap (-1) ρ).comp hparam)
  have hprofile := joinedLoop_affine_arc_energy_and_norm_bound a Γ haLip hΓ hperiod hInv
    (ψ.monotone ha₀b₀) hshort ha0 ha1
  have hrange : _root_.Set.MapsTo (periodicLoopCone (a 0) (joinedLoop_periodic a b))
      (_root_.Metric.closedBall (0 : ℂ) 1) (_root_.Metric.closedBall (a 0) η) :=
    periodicLoopCone_mapsTo_closedBall (a 0) (joinedLoop_periodic a b)
      (fun t => (hprofile.2.2.2.2.2.2.1 t).trans hsmall)
  refine ⟨ψbar, h, q, hψbar, hsame, hline, himage, hboundary, hqeq, hqLip, ?_,
    hseam, hcapTrace, ?_⟩
  · intro z hz
    rw [hqeq]
    obtain ⟨w, hw, rfl⟩ := himage.symm ▸ hz
    simpa only [Function.comp_apply, h.symm_apply_apply] using hrange hw
  · simpa only [NNReal.coe_one, one_pow, mul_one] using hqEnergy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_boundary_cap_in_ball_of_short_lift_increment then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_boundary_cap_in_ball_of_short_lift_increment"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_boundary_cap_in_ball_of_short_lift_increment ``Submission.DifferentialGeometry.Analysis.exists_boundary_cap_in_ball_of_short_lift_increment

end DifferentialGeometry.Analysis

end

end
