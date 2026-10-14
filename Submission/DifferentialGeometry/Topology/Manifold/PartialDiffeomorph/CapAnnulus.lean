import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.CompactGluing
import Mathlib.Geometry.Manifold.Instances.Sphere

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Metric
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology.Manifold

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_ball_chart_of_cap_and_annulus_eqOn_neighborhoods
    {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [T2Space M]
    (C T : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞)
    {L R : ℝ} (hL : 0 < L) (hLR : L < R)
    (hC : _root_.Metric.closedBall (0 : E3) L ⊆ C.source)
    (hT : _root_.Metric.closedBall (0 : E3) R \ _root_.Metric.ball (0 : E3) L ⊆ T.source)
    {O : Set E3} (hO : IsOpen O) (hSO : _root_.Metric.sphere (0 : E3) L ⊆ O)
    (heq : _root_.Set.EqOn C T O)
    (hinter : C '' _root_.Metric.closedBall (0 : E3) L ∩ T '' (_root_.Metric.closedBall (0 : E3) R \ _root_.Metric.ball (0 : E3) L) ⊆
      C '' _root_.Metric.sphere (0 : E3) L) :
    ∃ B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞,
      _root_.Metric.closedBall (0 : E3) 1 ⊆ B.source ∧
      (∀ z ∈ _root_.Metric.closedBall (0 : E3) L, B (R⁻¹ • z) = C z) ∧
      (∀ z ∈ _root_.Metric.closedBall (0 : E3) R \ _root_.Metric.ball (0 : E3) L, B (R⁻¹ • z) = T z) ∧
      B '' _root_.Metric.ball (0 : E3) 1 = C '' _root_.Metric.closedBall (0 : E3) L ∪
        T '' (_root_.Metric.ball (0 : E3) R \ _root_.Metric.ball (0 : E3) L) ∧
      ∃ V₀ V₁ : Set E3, IsOpen V₀ ∧ IsOpen V₁ ∧
        _root_.Metric.closedBall (0 : E3) L ⊆ V₀ ∧
        _root_.Metric.closedBall (0 : E3) R \ _root_.Metric.ball (0 : E3) L ⊆ V₁ ∧
        EqOn (fun z => B (R⁻¹ • z)) C V₀ ∧ _root_.Set.EqOn (fun z => B (R⁻¹ • z)) T V₁ := by
  have hR : 0 < R := hL.trans hLR
  let K₀ := _root_.Metric.closedBall (0 : E3) L
  let K₁ := _root_.Metric.closedBall (0 : E3) R \ _root_.Metric.ball (0 : E3) L
  have hK₁ : IsCompact K₁ := (_root_.ProperSpace.isCompact_closedBall (0 : E3) R).inter_right isOpen_ball.isClosed_compl
  have hseam : K₀ ∩ K₁ = _root_.Metric.sphere (0 : E3) L := by
    ext z
    simp only [K₀, K₁, _root_.Set.mem_inter_iff, _root_.Set.mem_sdiff, mem_closedBall_zero_iff,
      mem_ball_zero_iff, mem_sphere_zero_iff_norm, not_lt]
    constructor
    · rintro ⟨hl, _, hg⟩
      exact le_antisymm hl hg
    · intro hz
      exact ⟨hz.le, hz.le.trans hLR.le, hz.ge⟩
  have hcover : K₀ ∪ K₁ = _root_.Metric.closedBall (0 : E3) R := by
    apply subset_antisymm
    · exact _root_.Set.union_subset (_root_.Metric.closedBall_subset_closedBall hLR.le) _root_.Set.sdiff_subset
    · intro z hz
      by_cases h : z ∈ _root_.Metric.ball (0 : E3) L
      · exact Or.inl (_root_.Metric.ball_subset_closedBall h)
      · exact Or.inr ⟨hz, h⟩
  obtain ⟨F, U₀, U₁, hU₀o, hU₁o, hK₀U, hK₁U, hU, hFC, hFT⟩ :=
    PartialDiffeomorph.exists_eqOn_neighborhoods_of_isCompact C T
      (_root_.ProperSpace.isCompact_closedBall (0 : E3) L) hK₁ hC hT hO
      (hseam ▸ hSO) heq (hseam ▸ hinter)
  have hRF : _root_.Metric.closedBall (0 : E3) R ⊆ F.source := by
    rw [← hcover]
    exact (_root_.Set.union_subset_union hK₀U hK₁U).trans hU
  let D : E3 ≃ₘ[ℝ] E3 :=
    (LinearEquiv.smulOfNeZero ℝ E3 R hR.ne').toContinuousLinearEquiv.toDiffeomorph
  let B := D.toPartialDiffeomorph.trans F
  have hB (z : E3) : B z = F (R • z) := rfl
  have hBinv (z : E3) : B (R⁻¹ • z) = F z := by
    rw [hB, smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
  have hBsrc : _root_.Metric.closedBall (0 : E3) 1 ⊆ B.source := by
    intro z hz
    refine ⟨mem_univ _, ?_⟩
    apply hRF
    rw [mem_closedBall_zero_iff]
    change ‖R • z‖ ≤ R
    rw [norm_smul, Real.norm_of_nonneg hR.le]
    exact (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hz) hR.le).trans_eq (mul_one R)
  refine ⟨B, hBsrc, ?_, ?_, ?_, ?_⟩
  · intro z hz
    rw [hBinv]
    exact hFC (hK₀U hz)
  · intro z hz
    rw [hBinv]
    exact hFT (hK₁U hz)
  · ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hRz : R • z ∈ _root_.Metric.ball (0 : E3) R := by
        rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hR.le]
        exact (mul_lt_mul_of_pos_left (mem_ball_zero_iff.mp hz) hR).trans_eq (mul_one R)
      by_cases hzL : R • z ∈ _root_.Metric.closedBall (0 : E3) L
      · exact Or.inl ⟨R • z, hzL, (hFC (hK₀U hzL)).symm⟩
      · have hznot : R • z ∉ _root_.Metric.ball (0 : E3) L := fun h => hzL (_root_.Metric.ball_subset_closedBall h)
        exact Or.inr ⟨R • z, ⟨hRz, hznot⟩,
          (hFT (hK₁U ⟨ball_subset_closedBall hRz, hznot⟩)).symm⟩
    · rintro (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
      · refine ⟨R⁻¹ • z, ?_, ?_⟩
        · rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (inv_pos.mpr hR).le]
          exact (inv_mul_lt_iff₀ hR).mpr (by simpa only [mul_one] using
            (mem_closedBall_zero_iff.mp hz).trans_lt hLR)
        · rw [hBinv]
          exact hFC (hK₀U hz)
      · refine ⟨R⁻¹ • z, ?_, ?_⟩
        · rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (inv_pos.mpr hR).le]
          exact (inv_mul_lt_iff₀ hR).mpr (by simpa only [mul_one] using mem_ball_zero_iff.mp hz.1)
        · rw [hBinv]
          exact hFT (hK₁U ⟨ball_subset_closedBall hz.1, hz.2⟩)
  · exact ⟨U₀, U₁, hU₀o, hU₁o, hK₀U, hK₁U,
      fun z hz => (hBinv z).trans (hFC hz), fun z hz => (hBinv z).trans (hFT hz)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_ball_chart_of_cap_and_annulus_eqOn_neighborhoods then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_ball_chart_of_cap_and_annulus_eqOn_neighborhoods"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_ball_chart_of_cap_and_annulus_eqOn_neighborhoods ``Submission.DifferentialGeometry.Topology.Manifold.exists_ball_chart_of_cap_and_annulus_eqOn_neighborhoods

theorem exists_ball_chart_of_cap_and_annulus
    {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [T2Space M]
    (C T : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞)
    {L R : ℝ} (hL : 0 < L) (hLR : L < R)
    (hC : _root_.Metric.closedBall (0 : E3) L ⊆ C.source)
    (hT : _root_.Metric.closedBall (0 : E3) R \ _root_.Metric.ball (0 : E3) L ⊆ T.source)
    {O : Set E3} (hO : IsOpen O) (hSO : _root_.Metric.sphere (0 : E3) L ⊆ O)
    (heq : _root_.Set.EqOn C T O)
    (hinter : C '' _root_.Metric.closedBall (0 : E3) L ∩ T '' (_root_.Metric.closedBall (0 : E3) R \ _root_.Metric.ball (0 : E3) L) ⊆
      C '' _root_.Metric.sphere (0 : E3) L) :
    ∃ B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞,
      _root_.Metric.closedBall (0 : E3) 1 ⊆ B.source ∧
      (∀ z ∈ _root_.Metric.closedBall (0 : E3) L, B (R⁻¹ • z) = C z) ∧
      (∀ z ∈ _root_.Metric.closedBall (0 : E3) R \ _root_.Metric.ball (0 : E3) L, B (R⁻¹ • z) = T z) ∧
      B '' _root_.Metric.ball (0 : E3) 1 = C '' _root_.Metric.closedBall (0 : E3) L ∪
        T '' (_root_.Metric.ball (0 : E3) R \ _root_.Metric.ball (0 : E3) L) := by
  obtain ⟨B, hBs, hBC, hBT, hBi, _⟩ :=
    exists_ball_chart_of_cap_and_annulus_eqOn_neighborhoods C T hL hLR hC hT hO hSO heq hinter
  exact ⟨B, hBs, hBC, hBT, hBi⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_ball_chart_of_cap_and_annulus then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_ball_chart_of_cap_and_annulus"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_ball_chart_of_cap_and_annulus ``Submission.DifferentialGeometry.Topology.Manifold.exists_ball_chart_of_cap_and_annulus

end DifferentialGeometry.Topology.Manifold
