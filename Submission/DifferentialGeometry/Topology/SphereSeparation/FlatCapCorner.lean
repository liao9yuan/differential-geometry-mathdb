import Submission.DifferentialGeometry.Topology.Handle.CylinderCorner
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import Submission.DifferentialGeometry.Topology.SphereSeparation.FlatCapCylinderSides

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Metric
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Topology.SphereSeparation

private theorem exists_vertical_reflection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    ∃ J : (E × ℝ) ≃ₘ[ℝ] (E × ℝ),
      (∀ p, J p = (p.1, σ * p.2)) ∧ ∀ p, J.symm p = (p.1, σ * p.2) := by
  rcases hσ with rfl | rfl
  · exact ⟨Diffeomorph.refl 𝓘(ℝ, E × ℝ) (E × ℝ) ∞,
      fun p => by simp, fun p => by simp⟩
  · refine ⟨((ContinuousLinearEquiv.refl ℝ E).prodCongr
      (ContinuousLinearEquiv.neg ℝ : ℝ ≃L[ℝ] ℝ)).toDiffeomorph, ?_, ?_⟩
    · intro p
      change (p.1, -p.2) = (p.1, -1 * p.2)
      rw [neg_one_mul]
    · intro p
      change (p.1, -p.2) = (p.1, -1 * p.2)
      rw [neg_one_mul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_vertical_reflection
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.exists_vertical_reflection target :: scope.openDecls } }

private theorem exists_signed_cylinder_corner_chart
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
    (Ψ : (E × ℝ) ≃ₘ[ℝ] F) (v : _root_.Metric.sphere (0 : E) 1)
    {R b ρ σ : ℝ} (hR : 0 < R) (hRρ : R ^ 2 = 1 + ρ)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hb : 0 < b) (hσ : σ = 1 ∨ σ = -1) :
    ∃ c : PartialDiffeomorph 𝓘(ℝ, F) ((𝓡 n).prod 𝓘(ℝ, ℝ × ℝ))
        F (_root_.Metric.sphere (0 : E) 1 × (ℝ × ℝ)) ∞,
      c.source = Ψ '' {p : E × ℝ | p ∈ _root_.Metric.ball 0 R ×ˢ _root_.Set.Ioo (-b) b ∧ 1 - ρ < ‖p.1‖ ^ 2} ∧
      c.target = _root_.Set.univ ×ˢ (_root_.Set.Ioo (-ρ) ρ ×ˢ _root_.Set.Ioo (-b) b) ∧
      (∀ p : E × ℝ, c (Ψ p) =
        (DifferentialGeometry.Topology.Manifold.sphereDirection v p.1,
          (1 - ‖p.1‖ ^ 2, σ * p.2))) ∧
      ∀ ε : ℝ, ε < ρ → ε < b →
        {p : _root_.Metric.sphere (0 : E) 1 × (ℝ × ℝ) |
          0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 + p.2.2 ≤ ε} ⊆ c.target := by
  obtain ⟨J, hJ, hJi⟩ := exists_vertical_reflection (E := E) hσ
  let d := ((J.trans Ψ).symm.toPartialDiffeomorph).trans
    (PartialDiffeomorph.cylinderCorner (n := n) 1 v)
  let B : Set (_root_.Metric.sphere (0 : E) 1 × (ℝ × ℝ)) := _root_.Set.univ ×ˢ (_root_.Set.Ioo (-ρ) ρ ×ˢ _root_.Set.Ioo (-b) b)
  have hB : IsOpen B := isOpen_univ.prod (isOpen_Ioo.prod isOpen_Ioo)
  let c := (DifferentialGeometry.Topology.PartialDiffeomorph.restrict d.symm B hB).symm
  have hd (p : E × ℝ) : d (Ψ p) =
      (DifferentialGeometry.Topology.Manifold.sphereDirection v p.1,
        (1 - ‖p.1‖ ^ 2, σ * p.2)) := by
    change PartialDiffeomorph.cylinderCorner (n := n) 1 v (J.symm (Ψ.symm (Ψ p))) = _
    rw [Ψ.symm_apply_apply, hJi, PartialDiffeomorph.cylinderCorner_apply]
    norm_num
  have hds (p : E × ℝ) : Ψ p ∈ d.source ↔ p.1 ≠ 0 := by
    change (True ∧ J.symm (Ψ.symm (Ψ p)) ∈ (PartialDiffeomorph.cylinderCorner (n := n) 1 v).source) ↔ _
    rw [Ψ.symm_apply_apply, hJi, PartialDiffeomorph.cylinderCorner_source]
    simp
  have hdt : d.target = {p | p.2.1 < 1} := by
    change (PartialDiffeomorph.cylinderCorner (n := n) 1 v).target ∩ _ = _
    simp only [PartialDiffeomorph.cylinderCorner_target, one_pow]
    ext p
    change (p.2.1 < 1 ∧ True) ↔ p.2.1 < 1
    simp
  have hBt : B ⊆ d.target := by
    rw [hdt]
    intro p hp
    exact hp.2.1.2.trans_le hρ1
  have hct : c.target = B := by
    change d.target ∩ B = B
    exact inter_eq_right.mpr hBt
  have hcb (p : E × ℝ) : d (Ψ p) ∈ B ↔
      p ∈ _root_.Metric.ball (0 : E) R ×ˢ _root_.Set.Ioo (-b) b ∧ 1 - ρ < ‖p.1‖ ^ 2 := by
    rw [hd]
    change (True ∧ (-ρ < 1 - ‖p.1‖ ^ 2 ∧ 1 - ‖p.1‖ ^ 2 < ρ) ∧
      -b < σ * p.2 ∧ σ * p.2 < b) ↔ _
    have ht : (-b < σ * p.2 ∧ σ * p.2 < b) ↔ (-b < p.2 ∧ p.2 < b) := by
      rcases hσ with rfl | rfl
      · simp only [one_mul]
      · simp only [neg_one_mul]
        constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
    rw [ht]
    simp only [true_and, _root_.Set.mem_prod, mem_ball_zero_iff, _root_.Set.mem_Ioo]
    constructor
    · rintro ⟨⟨h₁, h₂⟩, ht⟩
      exact ⟨⟨by nlinarith [norm_nonneg p.1], ht⟩, by linarith⟩
    · rintro ⟨⟨hn, ht⟩, h₂⟩
      exact ⟨⟨by nlinarith [norm_nonneg p.1], by linarith⟩, ht⟩
  refine ⟨c, ?_, hct, ?_, ?_⟩
  · ext y
    obtain ⟨p, rfl⟩ := Ψ.surjective y
    change (Ψ p ∈ d.source ∧ d (Ψ p) ∈ B) ↔ Ψ p ∈ Ψ '' _
    rw [hds, hcb]
    constructor
    · intro hp
      exact ⟨p, hp.2, rfl⟩
    · rintro ⟨q, hq, hqp⟩
      have he : q = p := Ψ.injective hqp
      subst q
      refine ⟨?_, hq⟩
      intro hz
      have hh := hq.2
      rw [hz, norm_zero] at hh
      nlinarith
  · intro p
    change d (Ψ p) = _
    exact hd p
  · intro ε hερ hεb p hp
    rw [hct]
    exact ⟨mem_univ _, ⟨by linarith [hp.1], by linarith [hp.2.1, hp.2.2]⟩,
      by linarith [hp.2.1], by linarith [hp.1, hp.2.2]⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_signed_cylinder_corner_chart
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.exists_signed_cylinder_corner_chart target :: scope.openDecls } }

theorem exists_flat_cap_corner_chart
    {X E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
    {g : X → F} (d : SphereSides (_root_.Set.range g))
    (Ψ : (E × ℝ) ≃ₘ[ℝ] F) (v : _root_.Metric.sphere (0 : E) 1)
    {R b ρ σ : ℝ} (hR : 0 < R) (hRρ : R ^ 2 = 1 + ρ)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hb : 0 < b) (hσ : σ = 1 ∨ σ = -1)
    (htrace : ∀ p ∈ _root_.Metric.ball (0 : E) R ×ˢ _root_.Set.Ioo (-b) b,
      Ψ p ∈ _root_.Set.range g ↔ (‖p.1‖ ≤ 1 ∧ p.2 = 0) ∨ (‖p.1‖ = 1 ∧ 0 < σ * p.2)) :
    ∃ c : PartialDiffeomorph 𝓘(ℝ, F) ((𝓡 n).prod 𝓘(ℝ, ℝ × ℝ))
        F (_root_.Metric.sphere (0 : E) 1 × (ℝ × ℝ)) ∞,
      c.source = Ψ '' {p : E × ℝ | p ∈ _root_.Metric.ball 0 R ×ˢ _root_.Set.Ioo (-b) b ∧ 1 - ρ < ‖p.1‖ ^ 2} ∧
      c.target = _root_.Set.univ ×ˢ (_root_.Set.Ioo (-ρ) ρ ×ˢ _root_.Set.Ioo (-b) b) ∧
      (∀ p : E × ℝ, c (Ψ p) =
        (DifferentialGeometry.Topology.Manifold.sphereDirection v p.1,
          (1 - ‖p.1‖ ^ 2, σ * p.2))) ∧
      (∀ ε : ℝ, ε < ρ → ε < b →
        {p : _root_.Metric.sphere (0 : E) 1 × (ℝ × ℝ) |
          0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 + p.2.2 ≤ ε} ⊆ c.target) ∧
      ((∀ p ∈ c.target, c.toOpenPartialHomeomorph.symm p ∈ closure d.compactSide ↔
          0 ≤ p.2.1 ∧ 0 ≤ p.2.2) ∨
        (∀ p ∈ c.target, c.toOpenPartialHomeomorph.symm p ∈ closure d.compactSide ↔
          p.2.1 ≤ 0 ∨ p.2.2 ≤ 0)) := by
  obtain ⟨c, hcs, hct, hcoord, hstrip⟩ :=
    exists_signed_cylinder_corner_chart (n := n) Ψ v hR hRρ hρ hρ1 hb hσ
  have hσne : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  have hR1 : 1 < R := by nlinarith
  have hpull (q : _root_.Metric.sphere (0 : E) 1 × (ℝ × ℝ)) (hq : q ∈ c.target) :
      ∃ p ∈ _root_.Metric.ball (0 : E) R ×ˢ _root_.Set.Ioo (-b) b,
        Ψ p = c.toOpenPartialHomeomorph.symm q ∧
          q.2 = (1 - ‖p.1‖ ^ 2, σ * p.2) := by
    have hsource := c.toOpenPartialHomeomorph.map_target hq
    change c.toOpenPartialHomeomorph.symm q ∈ c.source at hsource
    rw [hcs] at hsource
    obtain ⟨p, hp, hpq⟩ := hsource
    refine ⟨p, hp.1, hpq, ?_⟩
    have hc := congrArg Prod.snd (hcoord p)
    change (c.toOpenPartialHomeomorph (Ψ p)).2 = _ at hc
    rwa [hpq, c.toOpenPartialHomeomorph.right_inv hq] at hc
  have hside :
      (∀ p ∈ _root_.Metric.ball (0 : E) R ×ˢ _root_.Set.Ioo (-b) b,
        Ψ p ∈ closure d.compactSide ↔ ‖p.1‖ ≤ 1 ∧ 0 ≤ σ * p.2) ∨
      (∀ p ∈ _root_.Metric.ball (0 : E) R ×ˢ _root_.Set.Ioo (-b) b,
        Ψ p ∈ closure d.compactSide ↔ 1 ≤ ‖p.1‖ ∨ σ * p.2 ≤ 0) := by
    rcases d.toTwoSidedSeparation.closed_sides_in_flat_cap_cylinder Ψ.toHomeomorph
      zero_lt_one hR1 hb hσne htrace with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h
  refine ⟨c, hcs, hct, hcoord, hstrip, ?_⟩
  rcases hside with hside | hside
  · left
    intro q hq
    obtain ⟨p, hp, hpq, hqcoord⟩ := hpull q hq
    rw [← hpq, hside p hp, hqcoord]
    apply and_congr_left
    intro _
    constructor <;> intro h <;> nlinarith [norm_nonneg p.1]
  · right
    intro q hq
    obtain ⟨p, hp, hpq, hqcoord⟩ := hpull q hq
    rw [← hpq, hside p hp, hqcoord]
    apply or_congr_left
    constructor <;> intro h <;> nlinarith [norm_nonneg p.1]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exists_flat_cap_corner_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exists_flat_cap_corner_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exists_flat_cap_corner_chart ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_flat_cap_corner_chart

theorem exists_flat_cap_corner_chart_in_cylinder
    {X E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
    {g : X → F} (d : SphereSides (_root_.Set.range g))
    (Ψ : (E × ℝ) ≃ₘ[ℝ] F) (v : _root_.Metric.sphere (0 : E) 1)
    {R₀ b σ : ℝ} (hR₀ : 1 < R₀) (hb : 0 < b) (hσ : σ = 1 ∨ σ = -1)
    (htrace : ∀ p ∈ _root_.Metric.ball (0 : E) R₀ ×ˢ _root_.Set.Ioo (-b) b,
      Ψ p ∈ _root_.Set.range g ↔ (‖p.1‖ ≤ 1 ∧ p.2 = 0) ∨ (‖p.1‖ = 1 ∧ 0 < σ * p.2)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∃ R : ℝ, 1 < R ∧ R < R₀ ∧ R ^ 2 = 1 + ρ ∧
      ∃ c : PartialDiffeomorph 𝓘(ℝ, F) ((𝓡 n).prod 𝓘(ℝ, ℝ × ℝ))
          F (_root_.Metric.sphere (0 : E) 1 × (ℝ × ℝ)) ∞,
        c.source = Ψ '' {p : E × ℝ | p ∈ _root_.Metric.ball 0 R ×ˢ _root_.Set.Ioo (-b) b ∧ 1 - ρ < ‖p.1‖ ^ 2} ∧
        c.target = _root_.Set.univ ×ˢ (_root_.Set.Ioo (-ρ) ρ ×ˢ _root_.Set.Ioo (-b) b) ∧
        (∀ p : E × ℝ, c (Ψ p) =
          (DifferentialGeometry.Topology.Manifold.sphereDirection v p.1,
            (1 - ‖p.1‖ ^ 2, σ * p.2))) ∧
        (∀ ε : ℝ, ε < ρ → ε < b →
          {p : _root_.Metric.sphere (0 : E) 1 × (ℝ × ℝ) |
            0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 + p.2.2 ≤ ε} ⊆ c.target) ∧
        ((∀ p ∈ c.target, c.toOpenPartialHomeomorph.symm p ∈ closure d.compactSide ↔
            0 ≤ p.2.1 ∧ 0 ≤ p.2.2) ∨
          (∀ p ∈ c.target, c.toOpenPartialHomeomorph.symm p ∈ closure d.compactSide ↔
            p.2.1 ≤ 0 ∨ p.2.2 ≤ 0)) := by
  let ρ := _root_.Min.min (1 / 2 : ℝ) ((R₀ ^ 2 - 1) / 2)
  have hgap : 0 < R₀ ^ 2 - 1 := by nlinarith
  have hρ : 0 < ρ := lt_min (by norm_num) (by positivity)
  have hρ1 : ρ ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hρR : ρ ≤ (R₀ ^ 2 - 1) / 2 := min_le_right _ _
  let R := Real.sqrt (1 + ρ)
  have hR : 0 < R := Real.sqrt_pos.mpr (by linarith)
  have hRρ : R ^ 2 = 1 + ρ := Real.sq_sqrt (by linarith)
  have hR1 : 1 < R := by nlinarith
  have hRR₀ : R < R₀ := by nlinarith
  refine ⟨ρ, hρ, hρ1, R, hR1, hRR₀, hRρ, ?_⟩
  apply exists_flat_cap_corner_chart (n := n) d Ψ v hR hRρ hρ hρ1 hb hσ
  intro p hp
  exact htrace p ⟨ball_subset_ball hRR₀.le hp.1, hp.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exists_flat_cap_corner_chart_in_cylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exists_flat_cap_corner_chart_in_cylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exists_flat_cap_corner_chart_in_cylinder ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_flat_cap_corner_chart_in_cylinder

end DifferentialGeometry.Topology.SphereSeparation
