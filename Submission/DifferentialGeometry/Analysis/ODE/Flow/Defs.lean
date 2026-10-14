import Submission.DifferentialGeometry.Analysis.ODE.Flow.LinearODE.Variational

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Set _root_.Function _root_.Filter _root_.Metric _root_.Asymptotics
open scoped _root_.Topology _root_.NNReal

namespace DifferentialGeometry
namespace Analysis
namespace ODE
namespace Flow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

structure IsLocalFlow (f : ℝ → E → E) (t₀ : ℝ) (x₀ : E) (r : ℝ≥0) (tmin tmax : ℝ)
    (Φ : E × ℝ → E) : Prop where
  minTime_le_initial : tmin ≤ t₀
  initial_le_maxTime : t₀ ≤ tmax
  apply_initial : ∀ x ∈ _root_.Metric.closedBall x₀ r, Φ ⟨x, t₀⟩ = x
  hasDerivWithinAt : ∀ x ∈ _root_.Metric.closedBall x₀ r, ∀ t ∈ _root_.Set.Icc tmin tmax,
    HasDerivWithinAt (fun s => Φ ⟨x, s⟩) (f t (Φ ⟨x, t⟩)) (_root_.Set.Icc tmin tmax) t
  continuousOn : ContinuousOn Φ (_root_.Metric.closedBall x₀ r ×ˢ _root_.Set.Icc tmin tmax)
  exists_lipschitz : ∃ L' : ℝ≥0, ∀ t ∈ _root_.Set.Icc tmin tmax,
    LipschitzOnWith L' (fun x : E => Φ ⟨x, t⟩) (_root_.Metric.closedBall x₀ r)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.Flow.IsLocalFlow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.Flow.IsLocalFlow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.Flow.IsLocalFlow ``Submission.DifferentialGeometry.Analysis.ODE.Flow.IsLocalFlow

namespace IsLocalFlow

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

omit [CompleteSpace E] in
lemma t₀_mem_Icc (h : IsLocalFlow f t₀ x₀ r tmin tmax Φ) : t₀ ∈ _root_.Set.Icc tmin tmax :=
  ⟨h.minTime_le_initial, h.initial_le_maxTime⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.Flow.IsLocalFlow.t₀_mem_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.Flow.IsLocalFlow.t₀_mem_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.Flow.IsLocalFlow.t₀_mem_Icc ``Submission.DifferentialGeometry.Analysis.ODE.Flow.IsLocalFlow.t₀_mem_Icc

omit [CompleteSpace E] in
lemma orbit_continuousOn (h : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (x : E) (hx : x ∈ _root_.Metric.closedBall x₀ r) :
    ContinuousOn (fun t : ℝ => Φ ⟨x, t⟩) (_root_.Set.Icc tmin tmax) :=
  fun t ht => (h.hasDerivWithinAt x hx t ht).continuousWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.Flow.IsLocalFlow.orbit_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.Flow.IsLocalFlow.orbit_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.Flow.IsLocalFlow.orbit_continuousOn ``Submission.DifferentialGeometry.Analysis.ODE.Flow.IsLocalFlow.orbit_continuousOn

end IsLocalFlow

omit [CompleteSpace E] in
lemma exists_isPicardLindelof_of_contDiffAt
    (f : ℝ → E → E) {t₀ : ℝ} {x₀ : E}
    (hf : ContDiffAt ℝ 1 (_root_.Function.uncurry f) (t₀, x₀)) :
    ∃ (ε : ℝ) (hε : 0 < ε) (a r L K : ℝ≥0) (_ : 0 < r),
      IsPicardLindelof f (tmin := t₀ - ε) (tmax := t₀ + ε)
        ⟨t₀, by simp [le_of_lt hε]⟩ x₀ a r L K := by
  obtain ⟨K₀, sNhd, hsNhd, hl⟩ := hf.exists_lipschitzOnWith
  obtain ⟨ρ, hρ_pos, hρ_sub⟩ := Metric.mem_nhds_iff.mp hsNhd
  set Lf := K₀ * ρ + ‖uncurry f (t₀, x₀)‖ + 1 with hLf_def
  have hLf_pos : 0 < Lf := by positivity
  have hLf_nn : 0 ≤ Lf := le_of_lt hLf_pos
  set a₀ : ℝ := ρ / 4 with ha₀_def
  have ha₀_pos : 0 < a₀ := by positivity
  have ha₀_nn : 0 ≤ a₀ := le_of_lt ha₀_pos
  have ha₀_le_half : a₀ ≤ ρ / 2 := by
    rw [ha₀_def]; linarith
  have hpair_in_sNhd :
      ∀ (p : ℝ × E), _root_.Dist.dist p (t₀, x₀) ≤ ρ / 2 → p ∈ sNhd := by
    intro p hp
    apply hρ_sub
    rw [Metric.mem_ball]
    linarith
  have hb_uncurry : ∀ (p : ℝ × E), _root_.Dist.dist p (t₀, x₀) ≤ ρ / 2 → ‖uncurry f p‖ ≤ Lf := by
    intro p hp
    have hp_in : p ∈ sNhd := hpair_in_sNhd p hp
    have h_base : (t₀, x₀) ∈ sNhd := hρ_sub (_root_.Metric.mem_ball_self hρ_pos)
    calc ‖uncurry f p‖
        ≤ ‖uncurry f p - _root_.Function.uncurry f (t₀, x₀)‖ + ‖uncurry f (t₀, x₀)‖ := norm_le_norm_sub_add _ _
      _ ≤ K₀ * _root_.Dist.dist p (t₀, x₀) + ‖uncurry f (t₀, x₀)‖ := by
          gcongr
          rw [dist_eq_norm]
          exact hl.norm_sub_le hp_in h_base
      _ ≤ K₀ * ρ + ‖uncurry f (t₀, x₀)‖ := by gcongr; linarith
      _ ≤ Lf := le_add_of_nonneg_right zero_le_one
  have hpair_in_iff :
      ∀ (t : ℝ) (x : E), t ∈ _root_.Set.Icc (t₀ - a₀) (t₀ + a₀) → _root_.Dist.dist x x₀ ≤ a₀ →
        dist ((t, x) : ℝ × E) (t₀, x₀) ≤ ρ / 2 := by
    intro t x ht hx
    rw [Prod.dist_eq]
    have htd : _root_.Dist.dist t t₀ ≤ a₀ := by
      rw [Real.dist_eq, abs_le]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hmx : _root_.Max.max (_root_.Dist.dist t t₀) (_root_.Dist.dist x x₀) ≤ a₀ := max_le htd hx
    linarith
  let aN : ℝ≥0 := ⟨a₀, ha₀_nn⟩
  let rN : ℝ≥0 := ⟨a₀ / 2, by positivity⟩
  let LN : ℝ≥0 := ⟨Lf, hLf_nn⟩
  have hb' : ∀ t ∈ _root_.Set.Icc (t₀ - a₀) (t₀ + a₀), ∀ x ∈ _root_.Metric.closedBall x₀ aN, ‖f t x‖ ≤ Lf := by
    intro t ht x hx
    have hx' : _root_.Dist.dist x x₀ ≤ a₀ := by
      have : _root_.Dist.dist x x₀ ≤ (aN : ℝ) := mem_closedBall.mp hx
      change _root_.Dist.dist x x₀ ≤ a₀ at this
      exact this
    have h_dist : _root_.Dist.dist ((t, x) : ℝ × E) (t₀, x₀) ≤ ρ / 2 := hpair_in_iff t x ht hx'
    exact hb_uncurry (t, x) h_dist
  have hLip : ∀ t ∈ _root_.Set.Icc (t₀ - a₀) (t₀ + a₀),
      LipschitzOnWith K₀ (f t) (_root_.Metric.closedBall x₀ aN) := by
    intro t ht
    refine LipschitzOnWith.of_dist_le_mul ?_
    intro x hx y hy
    have hxd : _root_.Dist.dist x x₀ ≤ a₀ := by
      have : _root_.Dist.dist x x₀ ≤ (aN : ℝ) := mem_closedBall.mp hx
      change _root_.Dist.dist x x₀ ≤ a₀ at this
      exact this
    have hyd : _root_.Dist.dist y x₀ ≤ a₀ := by
      have : _root_.Dist.dist y x₀ ≤ (aN : ℝ) := mem_closedBall.mp hy
      change _root_.Dist.dist y x₀ ≤ a₀ at this
      exact this
    have hpx_d : _root_.Dist.dist ((t, x) : ℝ × E) (t₀, x₀) ≤ ρ / 2 := hpair_in_iff t x ht hxd
    have hpy_d : _root_.Dist.dist ((t, y) : ℝ × E) (t₀, x₀) ≤ ρ / 2 := hpair_in_iff t y ht hyd
    have hpx_in : ((t, x) : ℝ × E) ∈ sNhd := hpair_in_sNhd _ hpx_d
    have hpy_in : ((t, y) : ℝ × E) ∈ sNhd := hpair_in_sNhd _ hpy_d
    have hdist : _root_.Dist.dist ((t, x) : ℝ × E) (t, y) = _root_.Dist.dist x y := by
      rw [Prod.dist_eq]; simp [dist_self]
    have hdle : _root_.Dist.dist (_root_.Function.uncurry f (t, x)) (_root_.Function.uncurry f (t, y)) ≤ K₀ * _root_.Dist.dist ((t, x) : ℝ × E) (t, y) :=
      hl.dist_le_mul _ hpx_in _ hpy_in
    rw [hdist] at hdle
    change _root_.Dist.dist (_root_.Function.uncurry f (t, x)) (_root_.Function.uncurry f (t, y)) ≤ K₀ * _root_.Dist.dist x y
    exact hdle
  have hcontT : ∀ x ∈ _root_.Metric.closedBall x₀ aN,
      ContinuousOn (fun t => f t x) (_root_.Set.Icc (t₀ - a₀) (t₀ + a₀)) := by
    intro x hx
    have hxd : _root_.Dist.dist x x₀ ≤ a₀ := by
      have : _root_.Dist.dist x x₀ ≤ (aN : ℝ) := mem_closedBall.mp hx
      change _root_.Dist.dist x x₀ ≤ a₀ at this
      exact this
    have h_cont : ContinuousOn (_root_.Function.uncurry f) sNhd := hl.continuousOn
    have hcomp : ContinuousOn (fun t : ℝ => (t, x)) (_root_.Set.Icc (t₀ - a₀) (t₀ + a₀)) :=
      continuousOn_id.prodMk continuousOn_const
    have hmaps : _root_.Set.MapsTo (fun t : ℝ => (t, x)) (_root_.Set.Icc (t₀ - a₀) (t₀ + a₀))
        sNhd := fun t ht => hpair_in_sNhd _ (hpair_in_iff t x ht hxd)
    exact h_cont.comp hcomp hmaps
  set ε := _root_.Min.min a₀ (a₀ / (2 * (Lf + 1))) with hε_def
  have hε_pos : 0 < ε := by
    apply lt_min ha₀_pos
    apply div_pos ha₀_pos
    have : (0 : ℝ) < Lf + 1 := by linarith
    linarith
  have hε_le_a : ε ≤ a₀ := min_le_left _ _
  have hε_le_quotient : ε ≤ a₀ / (2 * (Lf + 1)) := min_le_right _ _
  have hLf_eps : Lf * ε ≤ a₀ / 2 := by
    have h1 : Lf * ε ≤ Lf * (a₀ / (2 * (Lf + 1))) :=
      mul_le_mul_of_nonneg_left hε_le_quotient hLf_nn
    have h2 : Lf * (a₀ / (2 * (Lf + 1))) = (Lf / (Lf + 1)) * (a₀ / 2) := by
      field_simp
    have h3 : Lf / (Lf + 1) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    have h4 : (Lf / (Lf + 1)) * (a₀ / 2) ≤ 1 * (a₀ / 2) :=
      mul_le_mul_of_nonneg_right h3 (by linarith)
    linarith
  have hsub_t : _root_.Set.Icc (t₀ - ε) (t₀ + ε) ⊆ _root_.Set.Icc (t₀ - a₀) (t₀ + a₀) := by
    intro t ht
    refine ⟨by linarith [ht.1, hε_le_a], by linarith [ht.2, hε_le_a]⟩
  refine ⟨ε, hε_pos, aN, rN, LN, K₀, ?_, ?_⟩
  · change (0 : ℝ) < a₀ / 2
    positivity
  refine
  { lipschitzOnWith := ?_,
    continuousOn := ?_,
    norm_le := ?_,
    mul_max_le := ?_ }
  · intro t ht
    exact hLip t (hsub_t ht)
  · intro x hx
    exact (hcontT x hx).mono hsub_t
  · intro t ht x hx
    exact hb' t (hsub_t ht) x hx
  · change (LN : ℝ) * _root_.Max.max ((t₀ + ε) - t₀) (t₀ - (t₀ - ε)) ≤ (aN : ℝ) - (rN : ℝ)
    have hmax : _root_.Max.max ((t₀ + ε) - t₀) (t₀ - (t₀ - ε)) = ε := by
      have h1 : (t₀ + ε) - t₀ = ε := by ring
      have h2 : t₀ - (t₀ - ε) = ε := by ring
      rw [h1, h2, max_self]
    have h_a_sub_r : (aN : ℝ) - (rN : ℝ) = a₀ / 2 := by
      change a₀ - a₀ / 2 = a₀ / 2; ring
    rw [hmax, h_a_sub_r]
    change Lf * ε ≤ a₀ / 2
    exact hLf_eps

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.Flow.exists_isPicardLindelof_of_contDiffAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.Flow.exists_isPicardLindelof_of_contDiffAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.Flow.exists_isPicardLindelof_of_contDiffAt ``Submission.DifferentialGeometry.Analysis.ODE.Flow.exists_isPicardLindelof_of_contDiffAt

omit [CompleteSpace E] in
lemma exists_isPicardLindelof_of_contDiffOn_univ
    (f : ℝ → E → E) (hf : ContDiffOn ℝ 1 (_root_.Function.uncurry f) (Set.univ : Set (ℝ × E)))
    (t₀ : ℝ) (x₀ : E) :
    ∃ (ε : ℝ) (hε : 0 < ε) (a r L K : ℝ≥0) (_ : 0 < r),
      IsPicardLindelof f (tmin := t₀ - ε) (tmax := t₀ + ε)
        ⟨t₀, by simp [le_of_lt hε]⟩ x₀ a r L K :=
  exists_isPicardLindelof_of_contDiffAt f
    (hf.contDiffAt (IsOpen.mem_nhds isOpen_univ (_root_.Set.mem_univ _)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.Flow.exists_isPicardLindelof_of_contDiffOn_univ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.Flow.exists_isPicardLindelof_of_contDiffOn_univ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.Flow.exists_isPicardLindelof_of_contDiffOn_univ ``Submission.DifferentialGeometry.Analysis.ODE.Flow.exists_isPicardLindelof_of_contDiffOn_univ

theorem exists_isLocalFlow_of_contDiffAt
    (f : ℝ → E → E) {t₀ : ℝ} {x₀ : E}
    (hf : ContDiffAt ℝ 1 (_root_.Function.uncurry f) (t₀, x₀)) :
    ∃ (r : ℝ≥0) (ε : ℝ) (_ : 0 < r) (_ : 0 < ε) (Φ : E × ℝ → E),
      IsLocalFlow f t₀ x₀ r (t₀ - ε) (t₀ + ε) Φ := by
  obtain ⟨ε, hε, a, r, _, _, hr, hpl⟩ := exists_isPicardLindelof_of_contDiffAt f hf
  obtain ⟨Φlip, hΦ₁, L', hΦ_lip⟩ :=
    hpl.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
  set Φ : E × ℝ → E := _root_.Function.uncurry Φlip with hΦ_def
  have hΦ_cont : ContinuousOn Φ (_root_.Metric.closedBall x₀ r ×ˢ _root_.Set.Icc (t₀ - ε) (t₀ + ε)) := by
    apply continuousOn_prod_of_continuousOn_lipschitzOnWith _ L' _ hΦ_lip
    exact fun x hx => HasDerivWithinAt.continuousOn (hΦ₁ x hx).2
  refine ⟨r, ε, hr, hε, Φ, ?_⟩
  refine
  { minTime_le_initial := by linarith,
    initial_le_maxTime := by linarith,
    apply_initial := fun x hx => (hΦ₁ x hx).1,
    hasDerivWithinAt := fun x hx t ht => (hΦ₁ x hx).2 t ht,
    continuousOn := hΦ_cont,
    exists_lipschitz := ⟨L', hΦ_lip⟩ }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.Flow.exists_isLocalFlow_of_contDiffAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.Flow.exists_isLocalFlow_of_contDiffAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.Flow.exists_isLocalFlow_of_contDiffAt ``Submission.DifferentialGeometry.Analysis.ODE.Flow.exists_isLocalFlow_of_contDiffAt

theorem exists_isLocalFlow_of_contDiffOn_univ
    (f : ℝ → E → E) (hf : ContDiffOn ℝ 1 (_root_.Function.uncurry f) (Set.univ : Set (ℝ × E)))
    (t₀ : ℝ) (x₀ : E) :
    ∃ (r : ℝ≥0) (ε : ℝ) (_ : 0 < r) (_ : 0 < ε) (Φ : E × ℝ → E),
      IsLocalFlow f t₀ x₀ r (t₀ - ε) (t₀ + ε) Φ :=
  exists_isLocalFlow_of_contDiffAt f
    (hf.contDiffAt (IsOpen.mem_nhds isOpen_univ (_root_.Set.mem_univ _)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.Flow.exists_isLocalFlow_of_contDiffOn_univ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.Flow.exists_isLocalFlow_of_contDiffOn_univ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.Flow.exists_isLocalFlow_of_contDiffOn_univ ``Submission.DifferentialGeometry.Analysis.ODE.Flow.exists_isLocalFlow_of_contDiffOn_univ

theorem exists_isIntegralCurveAt_of_contDiffAt
    {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E}
    (hf : ContDiffAt ℝ 1 (_root_.Function.uncurry f) (t₀, x₀)) :
    ∃ γ : ℝ → E, IsIntegralCurveAt γ f t₀ ∧ γ t₀ = x₀ := by
  obtain ⟨r, ε, hr, hε, Φ, hΦ⟩ := exists_isLocalFlow_of_contDiffAt f hf
  refine ⟨fun t => Φ (x₀, t), ?_, hΦ.apply_initial x₀ (_root_.Metric.mem_closedBall_self hr.le)⟩
  apply IsIntegralCurveOn.isIntegralCurveAt (s := _root_.Set.Icc (t₀ - ε) (t₀ + ε))
  · exact hΦ.hasDerivWithinAt x₀ (_root_.Metric.mem_closedBall_self hr.le)
  · exact Icc_mem_nhds (by linarith) (by linarith)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.Flow.exists_isIntegralCurveAt_of_contDiffAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.Flow.exists_isIntegralCurveAt_of_contDiffAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.Flow.exists_isIntegralCurveAt_of_contDiffAt ``Submission.DifferentialGeometry.Analysis.ODE.Flow.exists_isIntegralCurveAt_of_contDiffAt

namespace IsLocalFlow

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

omit [CompleteSpace E] in
lemma continuousOn_fderiv_along_orbit
    (hflow : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf : ContDiffOn ℝ 1 (_root_.Function.uncurry f) (Set.univ : Set (ℝ × E)))
    (x : E) (hx : x ∈ _root_.Metric.closedBall x₀ r) :
    ContinuousOn (fun t => fderiv ℝ (f t) (Φ ⟨x, t⟩)) (_root_.Set.Icc tmin tmax) := by
  have hpartial : ContinuousOn (fun p : ℝ × E => fderiv ℝ (f p.1) p.2)
      (Set.univ : Set (ℝ × E)) := by
    have h := continuousOn_partialFDeriv_uncurry (f := f)
      (s := (Set.univ : Set ℝ)) (u := (Set.univ : Set E))
      (by rwa [Set.univ_prod_univ]) isOpen_univ isOpen_univ
    rwa [Set.univ_prod_univ] at h
  have horbit : ContinuousOn (fun t : ℝ => (t, Φ ⟨x, t⟩)) (_root_.Set.Icc tmin tmax) :=
    continuousOn_id.prodMk (hflow.orbit_continuousOn x hx)
  have hmaps : _root_.Set.MapsTo (fun t : ℝ => (t, Φ ⟨x, t⟩)) (_root_.Set.Icc tmin tmax) Set.univ :=
    fun _ _ => _root_.Set.mem_univ _
  exact hpartial.comp horbit hmaps

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.Flow.IsLocalFlow.continuousOn_fderiv_along_orbit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.Flow.IsLocalFlow.continuousOn_fderiv_along_orbit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.Flow.IsLocalFlow.continuousOn_fderiv_along_orbit ``Submission.DifferentialGeometry.Analysis.ODE.Flow.IsLocalFlow.continuousOn_fderiv_along_orbit

omit [CompleteSpace E] in
lemma exists_norm_fderiv_le_along_orbit
    (hflow : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf : ContDiffOn ℝ 1 (_root_.Function.uncurry f) (Set.univ : Set (ℝ × E)))
    (x : E) (hx : x ∈ _root_.Metric.closedBall x₀ r) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ _root_.Set.Icc tmin tmax, ‖fderiv ℝ (f t) (Φ ⟨x, t⟩)‖ ≤ M := by
  have hcont := hflow.continuousOn_fderiv_along_orbit hf x hx
  have hcontN : ContinuousOn (fun t => ‖fderiv ℝ (f t) (Φ ⟨x, t⟩)‖) (_root_.Set.Icc tmin tmax) :=
    continuous_norm.comp_continuousOn hcont
  rcases isCompact_Icc.exists_isMaxOn ⟨t₀, hflow.t₀_mem_Icc⟩ hcontN with ⟨t₁, _, ht₁_max⟩
  exact ⟨‖fderiv ℝ (f t₁) (Φ ⟨x, t₁⟩)‖, norm_nonneg _, fun t ht => ht₁_max ht⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.Flow.IsLocalFlow.exists_norm_fderiv_le_along_orbit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.Flow.IsLocalFlow.exists_norm_fderiv_le_along_orbit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.Flow.IsLocalFlow.exists_norm_fderiv_le_along_orbit ``Submission.DifferentialGeometry.Analysis.ODE.Flow.IsLocalFlow.exists_norm_fderiv_le_along_orbit

theorem exists_variationalSolutionOn_Ioo_along_orbit
    (hflow : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf : ContDiffOn ℝ 1 (_root_.Function.uncurry f) (Set.univ : Set (ℝ × E)))
    (ht₀_Ioo : t₀ ∈ _root_.Set.Ioo tmin tmax)
    (x : E) (hx : x ∈ _root_.Metric.closedBall x₀ r) (δ : E) :
    ∃ ε' : ℝ, 0 < ε' ∧ _root_.Set.Ioo (t₀ - ε') (t₀ + ε') ⊆ _root_.Set.Ioo tmin tmax ∧
      ∃ y : ℝ → E, IsVariationalSolutionOn f (fun s => Φ ⟨x, s⟩) δ t₀ y
        (_root_.Set.Ioo (t₀ - ε') (t₀ + ε')) := by
  have hcontα : ContinuousOn (fun s : ℝ => Φ ⟨x, s⟩) (_root_.Set.Ioo tmin tmax) :=
    (hflow.orbit_continuousOn x hx).mono _root_.Set.Ioo_subset_Icc_self
  have hf_open : ContDiffOn ℝ 1 (_root_.Function.uncurry f)
      ((_root_.Set.Ioo tmin tmax) ×ˢ (Set.univ : Set E)) := hf.mono (_root_.Set.subset_univ _)
  obtain ⟨ε', hε', hsub_s, y, hy⟩ :=
    exists_isVariationalSolutionOn_Ioo_local
      (f := f) (α := fun s => Φ ⟨x, s⟩) (s := _root_.Set.Ioo tmin tmax) (u := Set.univ)
      hf_open isOpen_Ioo isOpen_univ hcontα (fun _ _ => _root_.Set.mem_univ _) t₀ ht₀_Ioo δ
  exact ⟨ε', hε', hsub_s, y, hy⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.Flow.IsLocalFlow.exists_variationalSolutionOn_Ioo_along_orbit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.Flow.IsLocalFlow.exists_variationalSolutionOn_Ioo_along_orbit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.Flow.IsLocalFlow.exists_variationalSolutionOn_Ioo_along_orbit ``Submission.DifferentialGeometry.Analysis.ODE.Flow.IsLocalFlow.exists_variationalSolutionOn_Ioo_along_orbit

end IsLocalFlow

end Flow
end ODE
end Analysis
end DifferentialGeometry

end
