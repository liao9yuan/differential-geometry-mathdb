import Submission.DifferentialGeometry.Topology.Embedding.FlatCap
import Submission.DifferentialGeometry.Topology.Embedding.FlatCapRounding
import Submission.DifferentialGeometry.Topology.SphereSeparation.CornerRounding
import Submission.DifferentialGeometry.Topology.SphereSeparation.Transport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set _root_.Metric
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Topology.SphereSeparation

private theorem smoothAbs_corner_eq_iff {ε u t : ℝ} (hε : 0 < ε) (hεu : ε ≤ u) :
    Real.smoothAbs ε (u - t) = u + t ↔ t = 0 := by
  constructor
  · intro h
    have hl := (Real.smoothAbs.sub_abs_mem_Icc hε (u - t)).1
    have ht : 0 ≤ t := by have := le_abs_self (u - t); linarith
    have hs : ε ≤ u + t := by linarith
    have he : Real.smoothAbs ε |u - t| = Real.smoothAbs ε (u + t) := by
      rw [Real.smoothAbs.abs hε.ne', Real.smoothAbs.eq_self_of_le hε hs]
      exact h
    have hab := (Real.smoothAbs.strictMonoOn_Ici hε).injOn
      (show |u - t| ∈ _root_.Set.Ici 0 from abs_nonneg (u - t))
      (show u + t ∈ _root_.Set.Ici 0 by change 0 ≤ u + t; linarith) he
    rcases le_total 0 (u - t) with hz | hz
    · rw [abs_of_nonneg hz] at hab
      linarith
    · rw [abs_of_nonpos hz] at hab
      linarith
  · rintro rfl
    simp only [sub_zero, add_zero]
    exact Real.smoothAbs.eq_self_of_le hε hεu

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.smoothAbs_corner_eq_iff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.smoothAbs_corner_eq_iff target :: scope.openDecls } }

private theorem rounded_flat_cap_boundary_in_corner
    {X E F P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace P]
    {g k : X → F} (Ψ : (E × ℝ) ≃ₘ[ℝ] F)
    (c : OpenPartialHomeomorph F (P × (ℝ × ℝ)))
    {R b ε σ ρ : ℝ} (hε : 0 < ε) (hερ : ε < ρ) (hσ : σ = 1 ∨ σ = -1)
    (hsource : c.source = Ψ '' {p : E × ℝ | p ∈ _root_.Metric.ball 0 R ×ˢ _root_.Set.Ioo (-b) b ∧ 1 - ρ < ‖p.1‖ ^ 2})
    (hcoord : ∀ p ∈ _root_.Metric.ball (0 : E) R ×ˢ _root_.Set.Ioo (-b) b, 1 - ρ < ‖p.1‖ ^ 2 →
      (c (Ψ p)).2 = (1 - ‖p.1‖ ^ 2, σ * p.2))
    (hraw : ∀ p ∈ _root_.Metric.ball (0 : E) R ×ˢ _root_.Set.Ioo (-b) b,
      Ψ p ∈ _root_.Set.range g ↔ (‖p.1‖ ≤ 1 ∧ p.2 = 0) ∨ (‖p.1‖ = 1 ∧ 0 < σ * p.2))
    (hrange : _root_.Set.range k = (_root_.Set.range g \ Ψ '' (_root_.Metric.ball (0 : E) R ×ˢ _root_.Set.Ioo (-b) b)) ∪
      Ψ '' {p : E × ℝ | p ∈ _root_.Metric.ball 0 R ×ˢ _root_.Set.Ioo (-b) b ∧
        Real.smoothAbs ε (1 - ‖p.1‖ ^ 2 - σ * p.2) = 1 - ‖p.1‖ ^ 2 + σ * p.2}) :
    _root_.Set.range k = (_root_.Set.range g \ c.source) ∪ c.symm '' (c.target ∩
      {p | Real.smoothAbs ε (p.2.1 - p.2.2) = p.2.1 + p.2.2}) := by
  let U := _root_.Metric.ball (0 : E) R ×ˢ _root_.Set.Ioo (-b) b
  have hσne : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  have haxis (p : E × ℝ) (hp : p ∈ U) (hz : ‖p.1‖ ^ 2 ≤ 1 - ρ) :
      (Real.smoothAbs ε (1 - ‖p.1‖ ^ 2 - σ * p.2) = 1 - ‖p.1‖ ^ 2 + σ * p.2) ↔
        Ψ p ∈ _root_.Set.range g := by
    have hn : ‖p.1‖ < 1 := by nlinarith [norm_nonneg p.1]
    rw [hraw p hp]
    simp only [hn.le, true_and, hn.ne, false_and, or_false]
    exact (smoothAbs_corner_eq_iff hε (by linarith : ε ≤ 1 - ‖p.1‖ ^ 2)).trans
      (mul_eq_zero_iff_left hσne)
  have hcU : c.source ⊆ Ψ '' U := by
    rw [hsource]
    exact _root_.Set.image_mono (fun _ hp => hp.1)
  have hlocal (p : E × ℝ) (hp : p ∈ U) (hz : 1 - ρ < ‖p.1‖ ^ 2) :
      Ψ p ∈ c.source ∧
      (Real.smoothAbs ε ((c (Ψ p)).2.1 - (c (Ψ p)).2.2) =
        (c (Ψ p)).2.1 + (c (Ψ p)).2.2 ↔
        Real.smoothAbs ε (1 - ‖p.1‖ ^ 2 - σ * p.2) = 1 - ‖p.1‖ ^ 2 + σ * p.2) := by
    refine ⟨hsource ▸ ⟨p, ⟨hp, hz⟩, rfl⟩, ?_⟩
    rw [hcoord p hp hz]
  rw [hrange]
  ext y
  constructor
  · rintro (⟨hy, hn⟩ | ⟨p, hp, rfl⟩)
    · exact Or.inl ⟨hy, fun h => hn (hcU h)⟩
    · by_cases hz : ‖p.1‖ ^ 2 ≤ 1 - ρ
      · refine Or.inl ⟨(haxis p hp.1 hz).mp hp.2, ?_⟩
        rw [hsource]
        rintro ⟨q, hq, hqp⟩
        have he : q = p := Ψ.injective hqp
        exact (not_lt_of_ge hz) (he ▸ hq.2)
      · have hc := hlocal p hp.1 (lt_of_not_ge hz)
        exact Or.inr ⟨c (Ψ p), ⟨c.map_source hc.1, hc.2.mpr hp.2⟩, c.left_inv hc.1⟩
  · rintro (⟨hy, hn⟩ | ⟨q, hq, rfl⟩)
    · by_cases hU : y ∈ Ψ '' U
      · obtain ⟨p, hp, rfl⟩ := hU
        have hz : ‖p.1‖ ^ 2 ≤ 1 - ρ := by
          by_contra hz
          exact hn (hlocal p hp (lt_of_not_ge hz)).1
        exact Or.inr ⟨p, ⟨hp, (haxis p hp hz).mpr hy⟩, rfl⟩
      · exact Or.inl ⟨hy, hU⟩
    · have hs := c.map_target hq.1
      rw [hsource] at hs
      obtain ⟨p, hp, hpc⟩ := hs
      have he : c (Ψ p) = q := by rw [hpc, c.right_inv hq.1]
      refine Or.inr ⟨p, ⟨hp.1, ?_⟩, hpc⟩
      apply (hlocal p hp.1 hp.2).2.mp
      rw [he]
      exact hq.2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.rounded_flat_cap_boundary_in_corner
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.rounded_flat_cap_boundary_in_corner target :: scope.openDecls } }

private theorem exists_diffeomorph_flat_cap_rounding_boundary
    {X E F P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace P]
    {e f g : X → F}
    (Ψ : (E × ℝ) ≃ₘ[ℝ] F) (χ : E → X)
    (c : OpenPartialHomeomorph F (P × (ℝ × ℝ)))
    {D : Set X} {R b a ε σ ρ : ℝ} (hR : 1 < R) (ha : 0 < a) (hab : a < b)
    (hε : 0 < ε) (hε1 : ε < 1) (hεb : ε < b) (hερ : ε < ρ) (hσ : σ = 1 ∨ σ = -1)
    (hχD : χ '' _root_.Metric.closedBall (0 : E) 1 = D)
    (hcap : ∀ x ∈ _root_.Metric.closedBall (0 : E) 1,
      f (χ x) = Ψ (EuclideanGeometry.cylinderCap (σ * a) x))
    (hflat : ∀ x ∈ _root_.Metric.closedBall (0 : E) 1, g (χ x) = Ψ (x, 0))
    (hfix : _root_.Set.EqOn f e Dᶜ) (hgfix : _root_.Set.EqOn g e Dᶜ)
    (hret : ∀ p ∈ _root_.Metric.ball (0 : E) R ×ˢ _root_.Set.Ioo (-b) b,
      Ψ p ∈ e '' Dᶜ ↔ ‖p.1‖ = 1 ∧ 0 < σ * p.2)
    (hsource : c.source = Ψ '' {p : E × ℝ | p ∈ _root_.Metric.ball 0 R ×ˢ _root_.Set.Ioo (-b) b ∧ 1 - ρ < ‖p.1‖ ^ 2})
    (hcoord : ∀ p ∈ _root_.Metric.ball (0 : E) R ×ˢ _root_.Set.Ioo (-b) b, 1 - ρ < ‖p.1‖ ^ 2 →
      (c (Ψ p)).2 = (1 - ‖p.1‖ ^ 2, σ * p.2)) :
    ∃ Φ : F ≃ₘ[ℝ] F,
      _root_.Set.range (Φ ∘ f) = (_root_.Set.range g \ c.source) ∪ c.symm '' (c.target ∩
        {p | Real.smoothAbs ε (p.2.1 - p.2.2) = p.2.1 + p.2.2}) ∧
      ∃ K : Set F, IsCompact K ∧
        K ⊆ Ψ '' (_root_.Metric.ball (0 : E) R ×ˢ _root_.Set.Ioo (-b) b) ∧
        EqOn Φ id Kᶜ ∧ _root_.Set.EqOn Φ.symm id Kᶜ := by
  have htrace := EuclideanGeometry.mem_range_flat_cap_iff Ψ.injective χ hχD hflat hgfix hret
  obtain ⟨Φ, hΦ, hK⟩ := Diffeomorph.exists_flat_cap_rounding Ψ χ hR ha hab hε hε1 hεb hσ
    hχD hcap hflat hfix hgfix hret
  have hboundary := rounded_flat_cap_boundary_in_corner Ψ c hε hερ hσ hsource hcoord htrace hΦ
  exact ⟨Φ, hboundary, hK⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_diffeomorph_flat_cap_rounding_boundary
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.exists_diffeomorph_flat_cap_rounding_boundary target :: scope.openDecls } }

theorem exists_diffeomorph_flat_cap_rounding_closure
    {X E F P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace P] [CompactSpace P]
    {e f g : X → F} (df : SphereSides (_root_.Set.range f)) (dg : SphereSides (_root_.Set.range g))
    (Ψ : (E × ℝ) ≃ₘ[ℝ] F) (χ : E → X)
    (c : OpenPartialHomeomorph F (P × (ℝ × ℝ)))
    {D : Set X} {R b a ε σ ρ : ℝ} (hR : 1 < R) (ha : 0 < a) (hab : a < b)
    (hε : 0 < ε) (hε1 : ε < 1) (hεb : ε < b) (hερ : ε < ρ) (hσ : σ = 1 ∨ σ = -1)
    (hχD : χ '' _root_.Metric.closedBall (0 : E) 1 = D)
    (hcap : ∀ x ∈ _root_.Metric.closedBall (0 : E) 1,
      f (χ x) = Ψ (EuclideanGeometry.cylinderCap (σ * a) x))
    (hflat : ∀ x ∈ _root_.Metric.closedBall (0 : E) 1, g (χ x) = Ψ (x, 0))
    (hfix : _root_.Set.EqOn f e Dᶜ) (hgfix : _root_.Set.EqOn g e Dᶜ)
    (hret : ∀ p ∈ _root_.Metric.ball (0 : E) R ×ˢ _root_.Set.Ioo (-b) b,
      Ψ p ∈ e '' Dᶜ ↔ ‖p.1‖ = 1 ∧ 0 < σ * p.2)
    (hsource : c.source = Ψ '' {p : E × ℝ | p ∈ _root_.Metric.ball 0 R ×ˢ _root_.Set.Ioo (-b) b ∧ 1 - ρ < ‖p.1‖ ^ 2})
    (hcoord : ∀ p ∈ _root_.Metric.ball (0 : E) R ×ˢ _root_.Set.Ioo (-b) b, 1 - ρ < ‖p.1‖ ^ 2 →
      (c (Ψ p)).2 = (1 - ‖p.1‖ ^ 2, σ * p.2))
    (hraw : ∀ p ∈ c.target,
      c.symm p ∈ closure dg.compactSide ↔ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2)
    (hstrip : {p : P × (ℝ × ℝ) | 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 + p.2.2 ≤ ε} ⊆
      c.target) :
    ∃ Φ : F ≃ₘ[ℝ] F,
      Φ '' closure df.compactSide = c.smoothAbsQuadrantSet (closure dg.compactSide) ε ∧
      ∃ K : Set F, IsCompact K ∧
        K ⊆ Ψ '' (_root_.Metric.ball (0 : E) R ×ˢ _root_.Set.Ioo (-b) b) ∧
        EqOn Φ id Kᶜ ∧ _root_.Set.EqOn Φ.symm id Kᶜ := by
  obtain ⟨Φ, hboundary, hK⟩ := exists_diffeomorph_flat_cap_rounding_boundary Ψ χ c hR ha hab
    hε hε1 hεb hερ hσ hχD hcap hflat hfix hgfix hret hsource hcoord
  let d' := df.image Φ.toHomeomorph
  have hrange : Φ '' _root_.Set.range f = _root_.Set.range (Φ ∘ f) := (Set.range_comp Φ f).symm
  have hround := dg.closure_compactSide_smoothAbsQuadrantSet d' c hε hraw hstrip
    (hrange.trans hboundary)
  have himage : Φ '' closure df.compactSide = closure d'.compactSide := by
    change Φ '' closure df.compactSide = closure (Φ '' df.compactSide)
    exact Φ.toHomeomorph.image_closure df.compactSide
  exact ⟨Φ, himage.trans hround, hK⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exists_diffeomorph_flat_cap_rounding_closure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exists_diffeomorph_flat_cap_rounding_closure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exists_diffeomorph_flat_cap_rounding_closure ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_diffeomorph_flat_cap_rounding_closure

theorem exists_diffeomorph_flat_cap_reflex_rounding_closure
    {X E F P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace P] [CompactSpace P]
    {e f g : X → F} (df : SphereSides (_root_.Set.range f)) (dg : SphereSides (_root_.Set.range g))
    (Ψ : (E × ℝ) ≃ₘ[ℝ] F) (χ : E → X)
    (c : OpenPartialHomeomorph F (P × (ℝ × ℝ)))
    {D : Set X} {R b a ε σ ρ : ℝ} (hR : 1 < R) (ha : 0 < a) (hab : a < b)
    (hε : 0 < ε) (hε1 : ε < 1) (hεb : ε < b) (hερ : ε < ρ) (hσ : σ = 1 ∨ σ = -1)
    (hχD : χ '' _root_.Metric.closedBall (0 : E) 1 = D)
    (hcap : ∀ x ∈ _root_.Metric.closedBall (0 : E) 1,
      f (χ x) = Ψ (EuclideanGeometry.cylinderCap (σ * a) x))
    (hflat : ∀ x ∈ _root_.Metric.closedBall (0 : E) 1, g (χ x) = Ψ (x, 0))
    (hfix : _root_.Set.EqOn f e Dᶜ) (hgfix : _root_.Set.EqOn g e Dᶜ)
    (hret : ∀ p ∈ _root_.Metric.ball (0 : E) R ×ˢ _root_.Set.Ioo (-b) b,
      Ψ p ∈ e '' Dᶜ ↔ ‖p.1‖ = 1 ∧ 0 < σ * p.2)
    (hsource : c.source = Ψ '' {p : E × ℝ | p ∈ _root_.Metric.ball 0 R ×ˢ _root_.Set.Ioo (-b) b ∧ 1 - ρ < ‖p.1‖ ^ 2})
    (hcoord : ∀ p ∈ _root_.Metric.ball (0 : E) R ×ˢ _root_.Set.Ioo (-b) b, 1 - ρ < ‖p.1‖ ^ 2 →
      (c (Ψ p)).2 = (1 - ‖p.1‖ ^ 2, σ * p.2))
    (hraw : ∀ p ∈ c.target,
      c.symm p ∈ closure dg.compactSide ↔ p.2.1 ≤ 0 ∨ p.2.2 ≤ 0)
    (hstrip : (_root_.Set.univ : Set P) ×ˢ _root_.Metric.closedBall (0 : ℝ × ℝ) ε ⊆ c.target) :
    ∃ Φ : F ≃ₘ[ℝ] F,
      Φ '' closure df.compactSide = (closure dg.compactSide \ c.source) ∪ c.symm ''
        (c.target ∩ {p | p.2.1 + p.2.2 ≤ Real.smoothAbs ε (p.2.1 - p.2.2)}) ∧
      ∃ K : Set F, IsCompact K ∧
        K ⊆ Ψ '' (_root_.Metric.ball (0 : E) R ×ˢ _root_.Set.Ioo (-b) b) ∧
        EqOn Φ id Kᶜ ∧ _root_.Set.EqOn Φ.symm id Kᶜ := by
  obtain ⟨Φ, hboundary, hK⟩ := exists_diffeomorph_flat_cap_rounding_boundary Ψ χ c hR ha hab
    hε hε1 hεb hερ hσ hχD hcap hflat hfix hgfix hret hsource hcoord
  let d' := df.image Φ.toHomeomorph
  have hrange : Φ '' _root_.Set.range f = _root_.Set.range (Φ ∘ f) := (Set.range_comp Φ f).symm
  have hround := dg.closure_compactSide_smoothAbs_reflex d' c hε hraw hstrip
    (hrange.trans hboundary)
  have himage : Φ '' closure df.compactSide = closure d'.compactSide := by
    change Φ '' closure df.compactSide = closure (Φ '' df.compactSide)
    exact Φ.toHomeomorph.image_closure df.compactSide
  exact ⟨Φ, himage.trans hround, hK⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exists_diffeomorph_flat_cap_reflex_rounding_closure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exists_diffeomorph_flat_cap_reflex_rounding_closure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exists_diffeomorph_flat_cap_reflex_rounding_closure ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_diffeomorph_flat_cap_reflex_rounding_closure

end DifferentialGeometry.Topology.SphereSeparation
