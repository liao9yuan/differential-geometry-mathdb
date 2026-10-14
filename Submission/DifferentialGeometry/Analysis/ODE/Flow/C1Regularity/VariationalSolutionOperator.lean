import Submission.DifferentialGeometry.Analysis.ODE.Flow.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section


open _root_.Set _root_.Function _root_.Filter _root_.Metric _root_.Asymptotics _root_.Real
open scoped _root_.Topology _root_.NNReal

namespace DifferentialGeometry
namespace Analysis
namespace ODE
namespace Flow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

section IccToIciIic

variable {y : ℝ → E} {y' : E} {a b τ : ℝ}

omit [CompleteSpace E] in
lemma hasDerivWithinAt_Ici_of_Icc
    (h : HasDerivWithinAt y y' (_root_.Set.Icc a b) τ) (hτ : τ ∈ _root_.Set.Ico a b) :
    HasDerivWithinAt y y' (_root_.Set.Ici τ) τ := by
  apply h.mono_of_mem_nhdsWithin
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
  refine ⟨Ioo (a - 1) b, Ioo_mem_nhds (by linarith [hτ.1]) hτ.2, ?_⟩
  intro s hs
  refine ⟨hτ.1.trans hs.2, le_of_lt hs.1.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.Flow.hasDerivWithinAt_Ici_of_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.Flow.hasDerivWithinAt_Ici_of_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.Flow.hasDerivWithinAt_Ici_of_Icc ``Submission.DifferentialGeometry.Analysis.ODE.Flow.hasDerivWithinAt_Ici_of_Icc

omit [CompleteSpace E] in
lemma hasDerivWithinAt_Iic_of_Icc
    (h : HasDerivWithinAt y y' (_root_.Set.Icc a b) τ) (hτ : τ ∈ _root_.Set.Ioc a b) :
    HasDerivWithinAt y y' (_root_.Set.Iic τ) τ := by
  apply h.mono_of_mem_nhdsWithin
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
  refine ⟨Ioo a (b + 1), Ioo_mem_nhds hτ.1 (by linarith [hτ.2]), ?_⟩
  intro s hs
  refine ⟨le_of_lt hs.1.1, hs.2.trans hτ.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.Flow.hasDerivWithinAt_Iic_of_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.Flow.hasDerivWithinAt_Iic_of_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.Flow.hasDerivWithinAt_Iic_of_Icc ``Submission.DifferentialGeometry.Analysis.ODE.Flow.hasDerivWithinAt_Iic_of_Icc

end IccToIciIic

section UniformExistence

variable {f : ℝ → E → E} {α : ℝ → E} {t₀ : ℝ}

theorem exists_isVariationalSolutionOn_Icc_of_short
    {T M : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (hMT : M * T < 1)
    (hA_cont : ContinuousOn (fun t => fderiv ℝ (f t) (α t)) (_root_.Set.Icc (t₀ - T) (t₀ + T)))
    (hA_bd : ∀ t ∈ _root_.Set.Icc (t₀ - T) (t₀ + T), ‖fderiv ℝ (f t) (α t)‖ ≤ M)
    (δ : E) :
    ∃ y : ℝ → E, IsVariationalSolutionOn f α δ t₀ y (_root_.Set.Icc (t₀ - T) (t₀ + T)) := by
  set A : ℝ → E →L[ℝ] E := fun t => fderiv ℝ (f t) (α t) with hA_def
  set v : ℝ → E → E := fun t y => (A t) y with hv_def
  set r₀ : ℝ := ‖δ‖ with hr₀_def
  have hr₀_nn : 0 ≤ r₀ := norm_nonneg _
  have h1mMT_pos : 0 < 1 - M * T := by linarith
  set a₀ : ℝ := (r₀ + 1) / (1 - M * T) with ha₀_def
  have ha₀_pos : 0 < a₀ := div_pos (by linarith [hr₀_nn]) h1mMT_pos
  have ha₀_nn : 0 ≤ a₀ := le_of_lt ha₀_pos
  have hMaT_le : M * a₀ * T ≤ a₀ - r₀ := by
    have hkey : a₀ * (1 - M * T) = r₀ + 1 := by
      rw [ha₀_def]; field_simp
    have h1 : a₀ - M * a₀ * T = r₀ + 1 := by
      have : a₀ - M * a₀ * T = a₀ * (1 - M * T) := by ring
      rw [this, hkey]
    linarith
  let tmin : ℝ := t₀ - T
  let tmax : ℝ := t₀ + T
  have htmin_le_t₀ : tmin ≤ t₀ := by change t₀ - T ≤ t₀; linarith
  have ht₀_le_tmax : t₀ ≤ tmax := by change t₀ ≤ t₀ + T; linarith
  let t₀Icc : _root_.Set.Icc tmin tmax := ⟨t₀, ⟨htmin_le_t₀, ht₀_le_tmax⟩⟩
  let aN : ℝ≥0 := ⟨a₀, ha₀_nn⟩
  let rN : ℝ≥0 := ⟨r₀, hr₀_nn⟩
  let LN : ℝ≥0 := ⟨M * a₀, mul_nonneg hM ha₀_nn⟩
  let KN : ℝ≥0 := ⟨M, hM⟩
  have hpl : IsPicardLindelof v t₀Icc (0 : E) aN rN LN KN := by
    refine
    { lipschitzOnWith := ?_,
      continuousOn := ?_,
      norm_le := ?_,
      mul_max_le := ?_ }
    · intro t ht
      have hAτ_bd : ‖A t‖ ≤ M := hA_bd t ht
      have hlip : LipschitzWith KN (A t) := (A t).lipschitzWith_of_opNorm_le hAτ_bd
      exact hlip.lipschitzOnWith (s := _root_.Metric.closedBall (0 : E) aN)
    · intro y _
      have happly : Continuous (fun B : E →L[ℝ] E => B y) :=
        (ContinuousLinearMap.apply ℝ E y).continuous
      exact happly.comp_continuousOn hA_cont
    · intro t ht y hy
      have hAt_bd : ‖A t‖ ≤ M := hA_bd t ht
      have hy_norm : ‖y‖ ≤ a₀ := by
        have hy' : ‖y‖ ≤ (aN : ℝ) := by
          simpa [mem_closedBall_zero_iff] using hy
        change ‖y‖ ≤ (aN : ℝ)
        exact hy'
      change ‖v t y‖ ≤ (LN : ℝ)
      calc ‖v t y‖ = ‖(A t) y‖ := rfl
        _ ≤ ‖A t‖ * ‖y‖ := (A t).le_opNorm y
        _ ≤ M * a₀ := mul_le_mul hAt_bd hy_norm (norm_nonneg _) hM
    · change (LN : ℝ) * _root_.Max.max (tmax - t₀) (t₀ - tmin) ≤ (aN : ℝ) - (rN : ℝ)
      have hmax_eq : _root_.Max.max (tmax - t₀) (t₀ - tmin) = T := by
        have h1 : tmax - t₀ = T := by change (t₀ + T) - t₀ = T; ring
        have h2 : t₀ - tmin = T := by change t₀ - (t₀ - T) = T; ring
        rw [h1, h2]; exact max_self _
      rw [hmax_eq]
      change M * a₀ * T ≤ a₀ - r₀
      exact hMaT_le
  have hδ_mem : δ ∈ _root_.Metric.closedBall (0 : E) rN := by
    rw [mem_closedBall_zero_iff]; change ‖δ‖ ≤ r₀; rfl
  obtain ⟨y, hy_initial, hy_deriv⟩ :=
    hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt hδ_mem
  exact ⟨y, hy_initial, fun τ hτ => hy_deriv τ hτ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.Flow.exists_isVariationalSolutionOn_Icc_of_short then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.Flow.exists_isVariationalSolutionOn_Icc_of_short"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.Flow.exists_isVariationalSolutionOn_Icc_of_short ``Submission.DifferentialGeometry.Analysis.ODE.Flow.exists_isVariationalSolutionOn_Icc_of_short

end UniformExistence

section GronwallBound

variable {f : ℝ → E → E} {α : ℝ → E} {t₀ : ℝ}

omit [CompleteSpace E] in
theorem IsVariationalSolutionOn.norm_le_exp_of_mem_Icc
    {T M : ℝ} (hT : 0 ≤ T) (hM : 0 ≤ M)
    {δ : E} {y : ℝ → E}
    (hy : IsVariationalSolutionOn f α δ t₀ y (_root_.Set.Icc (t₀ - T) (t₀ + T)))
    (hA_bd : ∀ t ∈ _root_.Set.Icc (t₀ - T) (t₀ + T), ‖fderiv ℝ (f t) (α t)‖ ≤ M) :
    ∀ t ∈ _root_.Set.Icc (t₀ - T) (t₀ + T), ‖y t‖ ≤ ‖δ‖ * _root_.Real.exp (M * T) := by
  intro t ht
  set A : ℝ → E →L[ℝ] E := fun t => fderiv ℝ (f t) (α t) with hA_def
  rcases le_or_gt t₀ t with htge | htlt
  · have hsub_R : _root_.Set.Icc t₀ (t₀ + T) ⊆ _root_.Set.Icc (t₀ - T) (t₀ + T) := _root_.Set.Icc_subset_Icc_left (by linarith)
    have hy_contR : ContinuousOn y (_root_.Set.Icc t₀ (t₀ + T)) := hy.continuousOn.mono hsub_R
    have hy_dR : ∀ τ ∈ _root_.Set.Ico t₀ (t₀ + T),
        HasDerivWithinAt y ((A τ) (y τ)) (_root_.Set.Ici τ) τ := by
      intro τ hτ
      have hτ_in : τ ∈ _root_.Set.Icc (t₀ - T) (t₀ + T) := hsub_R ⟨hτ.1, le_of_lt hτ.2⟩
      have hd := hy.2 τ hτ_in
      have hτ_Ico : τ ∈ _root_.Set.Ico (t₀ - T) (t₀ + T) := ⟨hτ_in.1, hτ.2⟩
      exact hasDerivWithinAt_Ici_of_Icc hd hτ_Ico
    have hbound : ∀ τ ∈ _root_.Set.Ico t₀ (t₀ + T), ‖(A τ) (y τ)‖ ≤ M * ‖y τ‖ + 0 := by
      intro τ hτ
      have hτ_in : τ ∈ _root_.Set.Icc (t₀ - T) (t₀ + T) := hsub_R ⟨hτ.1, le_of_lt hτ.2⟩
      calc ‖(A τ) (y τ)‖ ≤ ‖A τ‖ * ‖y τ‖ := (A τ).le_opNorm _
        _ ≤ M * ‖y τ‖ := by have := hA_bd τ hτ_in; gcongr
        _ = M * ‖y τ‖ + 0 := by ring
    have hinit : ‖y t₀‖ ≤ ‖δ‖ := by rw [hy.1]
    have hgr := norm_le_gronwallBound_of_norm_deriv_right_le
      (f := y) (f' := fun τ => (A τ) (y τ))
      (δ := ‖δ‖) (K := M) (ε := 0)
      hy_contR hy_dR hinit hbound
    have hht_R : t ∈ _root_.Set.Icc t₀ (t₀ + T) := ⟨htge, ht.2⟩
    have hgr_t := hgr t hht_R
    rw [gronwallBound_ε0] at hgr_t
    have hexp_mono : _root_.Real.exp (M * (t - t₀)) ≤ _root_.Real.exp (M * T) := by
      apply exp_le_exp.mpr
      have : t - t₀ ≤ T := by linarith [ht.2]
      nlinarith [hM, this]
    calc ‖y t‖ ≤ ‖δ‖ * _root_.Real.exp (M * (t - t₀)) := hgr_t
      _ ≤ ‖δ‖ * _root_.Real.exp (M * T) := by
        apply mul_le_mul_of_nonneg_left hexp_mono (norm_nonneg _)
  · have hsub_L : _root_.Set.Icc (t₀ - T) t₀ ⊆ _root_.Set.Icc (t₀ - T) (t₀ + T) := _root_.Set.Icc_subset_Icc_right (by linarith)
    have hy_contL : ContinuousOn y (_root_.Set.Icc (t₀ - T) t₀) := hy.continuousOn.mono hsub_L
    have hy_dL : ∀ τ ∈ _root_.Set.Ioc (t₀ - T) t₀,
        HasDerivWithinAt y ((A τ) (y τ)) (_root_.Set.Iic τ) τ := by
      intro τ hτ
      have hτ_in : τ ∈ _root_.Set.Icc (t₀ - T) (t₀ + T) := hsub_L ⟨le_of_lt hτ.1, hτ.2⟩
      have hd := hy.2 τ hτ_in
      have hτ_Ioc : τ ∈ _root_.Set.Ioc (t₀ - T) (t₀ + T) := ⟨hτ.1, by linarith [hτ.2]⟩
      exact hasDerivWithinAt_Iic_of_Icc hd hτ_Ioc
    let φ : ℝ → ℝ := fun s => 2 * t₀ - s
    let z : ℝ → E := y ∘ φ
    have hφ_cont : Continuous φ := by
      change Continuous (fun s : ℝ => 2 * t₀ - s); fun_prop
    have hz_cont : ContinuousOn z (_root_.Set.Icc t₀ (t₀ + T)) := by
      apply hy_contL.comp hφ_cont.continuousOn
      intro s hs
      have h1 : t₀ ≤ s := hs.1
      have h2 : s ≤ t₀ + T := hs.2
      refine ⟨?_, ?_⟩
      · change t₀ - T ≤ 2 * t₀ - s; linarith
      · change 2 * t₀ - s ≤ t₀; linarith
    have hz_d : ∀ τ ∈ _root_.Set.Ico t₀ (t₀ + T),
        HasDerivWithinAt z (-(A (2 * t₀ - τ)) (y (2 * t₀ - τ))) (_root_.Set.Ici τ) τ := by
      intro τ hτ
      have hreflect_τ : 2 * t₀ - τ ∈ _root_.Set.Ioc (t₀ - T) t₀ :=
        ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
      have hy_d_τ := hy_dL (2 * t₀ - τ) hreflect_τ
      have hφ : HasDerivWithinAt φ (-1 : ℝ) (_root_.Set.Ici τ) τ := by
        have h1 : HasDerivAt φ (-1 : ℝ) τ := by
          have h2 : HasDerivAt (fun s : ℝ => 2 * t₀ - s) (-1 : ℝ) τ := by
            exact (hasDerivAt_id' τ).const_sub (2 * t₀)
          exact h2
        exact h1.hasDerivWithinAt
      have hmaps : _root_.Set.MapsTo φ (_root_.Set.Ici τ) (_root_.Set.Iic (2 * t₀ - τ)) := by
        intro s hs
        have hs_le : τ ≤ s := hs
        change 2 * t₀ - s ≤ 2 * t₀ - τ
        linarith
      have hcomp := HasDerivWithinAt.scomp (g₁ := y)
        (h := φ) τ hy_d_τ hφ hmaps
      change HasDerivWithinAt z _ (_root_.Set.Ici τ) τ
      convert hcomp using 1
      module
    have hbound : ∀ τ ∈ _root_.Set.Ico t₀ (t₀ + T),
        ‖-(A (2 * t₀ - τ)) (y (2 * t₀ - τ))‖ ≤ M * ‖z τ‖ + 0 := by
      intro τ hτ
      have hreflect : 2 * t₀ - τ ∈ _root_.Set.Icc (t₀ - T) (t₀ + T) := by
        refine ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
      rw [norm_neg]
      change ‖(A (2 * t₀ - τ)) (y (2 * t₀ - τ))‖ ≤ M * ‖z τ‖ + 0
      calc ‖(A (2 * t₀ - τ)) (y (2 * t₀ - τ))‖
          ≤ ‖A (2 * t₀ - τ)‖ * ‖y (2 * t₀ - τ)‖ := (A (2 * t₀ - τ)).le_opNorm _
        _ ≤ M * ‖z τ‖ := by
            have := hA_bd (2 * t₀ - τ) hreflect
            change _ * _ ≤ M * ‖y (2 * t₀ - τ)‖
            gcongr
        _ = M * ‖z τ‖ + 0 := by ring
    have hzinit : ‖z t₀‖ ≤ ‖δ‖ := by
      change ‖y (2 * t₀ - t₀)‖ ≤ ‖δ‖
      have h0 : 2 * t₀ - t₀ = t₀ := by ring
      rw [h0, hy.1]
    have hgr := norm_le_gronwallBound_of_norm_deriv_right_le
      (f := z) (f' := fun τ => -(A (2 * t₀ - τ)) (y (2 * t₀ - τ)))
      (δ := ‖δ‖) (K := M) (ε := 0)
      hz_cont hz_d hzinit hbound
    set τ' := 2 * t₀ - t with hτ'_def
    have hτ'_in : τ' ∈ _root_.Set.Icc t₀ (t₀ + T) := ⟨by linarith [htlt.le], by linarith [ht.1]⟩
    have hgr_τ' := hgr τ' hτ'_in
    rw [gronwallBound_ε0] at hgr_τ'
    have hexp_mono : _root_.Real.exp (M * (τ' - t₀)) ≤ _root_.Real.exp (M * T) := by
      apply exp_le_exp.mpr
      have : τ' - t₀ ≤ T := by change 2 * t₀ - t - t₀ ≤ T; linarith [ht.1]
      nlinarith [hM, this]
    have hz_eq : z τ' = y t := by
      change y (2 * t₀ - τ') = y t
      have : 2 * t₀ - τ' = t := by change 2 * t₀ - (2 * t₀ - t) = t; ring
      rw [this]
    rw [hz_eq] at hgr_τ'
    calc ‖y t‖ ≤ ‖δ‖ * _root_.Real.exp (M * (τ' - t₀)) := hgr_τ'
      _ ≤ ‖δ‖ * _root_.Real.exp (M * T) := by
        apply mul_le_mul_of_nonneg_left hexp_mono (norm_nonneg _)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Analysis.ODE.Flow.IsVariationalSolutionOn
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.Flow.IsVariationalSolutionOn.norm_le_exp_of_mem_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.Flow.IsVariationalSolutionOn.norm_le_exp_of_mem_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.Flow.IsVariationalSolutionOn.norm_le_exp_of_mem_Icc ``Submission.DifferentialGeometry.Analysis.ODE.Flow.IsVariationalSolutionOn.norm_le_exp_of_mem_Icc

end GronwallBound

section LinearMap

variable {f : ℝ → E → E} {α : ℝ → E} {t₀ : ℝ}

omit [CompleteSpace E] in
theorem IsVariationalSolutionOn.unique_Icc
    {T : ℝ} (hT : 0 < T)
    (hA_cont : ContinuousOn (fun t => fderiv ℝ (f t) (α t)) (_root_.Set.Icc (t₀ - T) (t₀ + T)))
    {δ : E} {y₁ y₂ : ℝ → E}
    (h₁ : IsVariationalSolutionOn f α δ t₀ y₁ (_root_.Set.Icc (t₀ - T) (t₀ + T)))
    (h₂ : IsVariationalSolutionOn f α δ t₀ y₂ (_root_.Set.Icc (t₀ - T) (t₀ + T))) :
    EqOn y₁ y₂ (_root_.Set.Icc (t₀ - T) (t₀ + T)) := by
  intro t ht
  have hcomb := h₁.linear_combination (c₁ := 1) (c₂ := -1) h₂
  have hdiff : IsVariationalSolutionOn f α (0 : E) t₀ (fun s => y₁ s - y₂ s)
      (_root_.Set.Icc (t₀ - T) (t₀ + T)) := by
    have hsimp : (1 : ℝ) • δ + (-1 : ℝ) • δ = (0 : E) := by simp
    have hfun_eq : (fun s => (1 : ℝ) • y₁ s + (-1 : ℝ) • y₂ s) = fun s => y₁ s - y₂ s := by
      funext s
      rw [one_smul]
      module
    rw [hsimp, hfun_eq] at hcomb
    exact hcomb
  obtain ⟨M, hM_nn, hMbd⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ _root_.Set.Icc (t₀ - T) (t₀ + T),
      ‖fderiv ℝ (f τ) (α τ)‖ ≤ M := by
    have hcont_norm : ContinuousOn (fun τ => ‖fderiv ℝ (f τ) (α τ)‖)
        (_root_.Set.Icc (t₀ - T) (t₀ + T)) :=
      continuous_norm.comp_continuousOn hA_cont
    have hcpt : IsCompact (_root_.Set.Icc (t₀ - T) (t₀ + T)) := _root_.CompactIccSpace.isCompact_Icc
    have hne : (_root_.Set.Icc (t₀ - T) (t₀ + T)).Nonempty := ⟨t₀, ⟨by linarith, by linarith⟩⟩
    rcases hcpt.exists_isMaxOn hne hcont_norm with ⟨τ₁, _, hτ₁_max⟩
    exact ⟨‖fderiv ℝ (f τ₁) (α τ₁)‖, norm_nonneg _, fun τ hτ => hτ₁_max hτ⟩
  have hbd := IsVariationalSolutionOn.norm_le_exp_of_mem_Icc (le_of_lt hT) hM_nn hdiff hMbd t ht
  rw [norm_zero, _root_.MulZeroClass.zero_mul] at hbd
  have hzero : y₁ t - y₂ t = 0 := norm_le_zero_iff.mp hbd
  exact sub_eq_zero.mp hzero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.Flow.IsVariationalSolutionOn.unique_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.Flow.IsVariationalSolutionOn.unique_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.Flow.IsVariationalSolutionOn.unique_Icc ``Submission.DifferentialGeometry.Analysis.ODE.Flow.IsVariationalSolutionOn.unique_Icc

def variationalSolutionFun
    {T M : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (hMT : M * T < 1)
    (hA_cont : ContinuousOn (fun t => fderiv ℝ (f t) (α t)) (_root_.Set.Icc (t₀ - T) (t₀ + T)))
    (hA_bd : ∀ t ∈ _root_.Set.Icc (t₀ - T) (t₀ + T), ‖fderiv ℝ (f t) (α t)‖ ≤ M) :
    E → ℝ → E :=
  fun δ => (exists_isVariationalSolutionOn_Icc_of_short hT hM hMT hA_cont hA_bd δ).choose

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.Flow.variationalSolutionFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.Flow.variationalSolutionFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.Flow.variationalSolutionFun ``Submission.DifferentialGeometry.Analysis.ODE.Flow.variationalSolutionFun

lemma variationalSolutionFun_isSolution
    {T M : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (hMT : M * T < 1)
    (hA_cont : ContinuousOn (fun t => fderiv ℝ (f t) (α t)) (_root_.Set.Icc (t₀ - T) (t₀ + T)))
    (hA_bd : ∀ t ∈ _root_.Set.Icc (t₀ - T) (t₀ + T), ‖fderiv ℝ (f t) (α t)‖ ≤ M) (δ : E) :
    IsVariationalSolutionOn f α δ t₀
      (variationalSolutionFun hT hM hMT hA_cont hA_bd δ)
      (_root_.Set.Icc (t₀ - T) (t₀ + T)) :=
  (exists_isVariationalSolutionOn_Icc_of_short hT hM hMT hA_cont hA_bd δ).choose_spec

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.Flow.variationalSolutionFun_isSolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.Flow.variationalSolutionFun_isSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.Flow.variationalSolutionFun_isSolution ``Submission.DifferentialGeometry.Analysis.ODE.Flow.variationalSolutionFun_isSolution

lemma variationalSolutionFun_linear
    {T M : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (hMT : M * T < 1)
    (hA_cont : ContinuousOn (fun t => fderiv ℝ (f t) (α t)) (_root_.Set.Icc (t₀ - T) (t₀ + T)))
    (hA_bd : ∀ t ∈ _root_.Set.Icc (t₀ - T) (t₀ + T), ‖fderiv ℝ (f t) (α t)‖ ≤ M)
    (c₁ c₂ : ℝ) (δ₁ δ₂ : E) {t : ℝ} (ht : t ∈ _root_.Set.Icc (t₀ - T) (t₀ + T)) :
    variationalSolutionFun hT hM hMT hA_cont hA_bd (c₁ • δ₁ + c₂ • δ₂) t
      = c₁ • variationalSolutionFun hT hM hMT hA_cont hA_bd δ₁ t
        + c₂ • variationalSolutionFun hT hM hMT hA_cont hA_bd δ₂ t := by
  set vSolution := variationalSolutionFun hT hM hMT hA_cont hA_bd with hvSolution
  set y₁ := vSolution δ₁ with hy₁
  set y₂ := vSolution δ₂ with hy₂
  set y₁₂ := vSolution (c₁ • δ₁ + c₂ • δ₂) with hy₁₂
  have h₁ : IsVariationalSolutionOn f α δ₁ t₀ y₁ (_root_.Set.Icc (t₀ - T) (t₀ + T)) :=
    variationalSolutionFun_isSolution hT hM hMT hA_cont hA_bd δ₁
  have h₂ : IsVariationalSolutionOn f α δ₂ t₀ y₂ (_root_.Set.Icc (t₀ - T) (t₀ + T)) :=
    variationalSolutionFun_isSolution hT hM hMT hA_cont hA_bd δ₂
  have h₁₂_alt : IsVariationalSolutionOn f α (c₁ • δ₁ + c₂ • δ₂) t₀
      (fun s => c₁ • y₁ s + c₂ • y₂ s) (_root_.Set.Icc (t₀ - T) (t₀ + T)) :=
    h₁.linear_combination (c₁ := c₁) (c₂ := c₂) h₂
  have h₁₂ : IsVariationalSolutionOn f α (c₁ • δ₁ + c₂ • δ₂) t₀ y₁₂
      (_root_.Set.Icc (t₀ - T) (t₀ + T)) :=
    variationalSolutionFun_isSolution hT hM hMT hA_cont hA_bd (c₁ • δ₁ + c₂ • δ₂)
  exact (IsVariationalSolutionOn.unique_Icc hT hA_cont h₁₂ h₁₂_alt) ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.Flow.variationalSolutionFun_linear then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.Flow.variationalSolutionFun_linear"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.Flow.variationalSolutionFun_linear ``Submission.DifferentialGeometry.Analysis.ODE.Flow.variationalSolutionFun_linear

lemma variationalSolutionFun_norm_le
    {T M : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (hMT : M * T < 1)
    (hA_cont : ContinuousOn (fun t => fderiv ℝ (f t) (α t)) (_root_.Set.Icc (t₀ - T) (t₀ + T)))
    (hA_bd : ∀ t ∈ _root_.Set.Icc (t₀ - T) (t₀ + T), ‖fderiv ℝ (f t) (α t)‖ ≤ M)
    (δ : E) {t : ℝ} (ht : t ∈ _root_.Set.Icc (t₀ - T) (t₀ + T)) :
    ‖variationalSolutionFun hT hM hMT hA_cont hA_bd δ t‖ ≤ _root_.Real.exp (M * T) * ‖δ‖ := by
  have hsol := variationalSolutionFun_isSolution hT hM hMT hA_cont hA_bd δ
  have hbd := IsVariationalSolutionOn.norm_le_exp_of_mem_Icc
    (le_of_lt hT) hM hsol hA_bd t ht
  rw [mul_comm (‖δ‖) (_root_.Real.exp (M * T))] at hbd
  exact hbd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.Flow.variationalSolutionFun_norm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.Flow.variationalSolutionFun_norm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.Flow.variationalSolutionFun_norm_le ``Submission.DifferentialGeometry.Analysis.ODE.Flow.variationalSolutionFun_norm_le

def variationalLinearMapAt
    {T M : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (hMT : M * T < 1)
    (hA_cont : ContinuousOn (fun t => fderiv ℝ (f t) (α t)) (_root_.Set.Icc (t₀ - T) (t₀ + T)))
    (hA_bd : ∀ t ∈ _root_.Set.Icc (t₀ - T) (t₀ + T), ‖fderiv ℝ (f t) (α t)‖ ≤ M)
    {t : ℝ} (ht : t ∈ _root_.Set.Icc (t₀ - T) (t₀ + T)) :
    E →L[ℝ] E := by
  let L : E →ₗ[ℝ] E :=
  { toFun := fun δ => variationalSolutionFun hT hM hMT hA_cont hA_bd δ t,
    map_add' := fun δ₁ δ₂ => by
      have h := variationalSolutionFun_linear hT hM hMT hA_cont hA_bd 1 1 δ₁ δ₂ ht
      simpa using h,
    map_smul' := fun c δ => by
      have h0 :
          variationalSolutionFun hT hM hMT hA_cont hA_bd ((0 : ℝ) • δ + (0 : ℝ) • δ) t
            = (0 : ℝ) • variationalSolutionFun hT hM hMT hA_cont hA_bd δ t
              + (0 : ℝ) • variationalSolutionFun hT hM hMT hA_cont hA_bd δ t :=
        variationalSolutionFun_linear hT hM hMT hA_cont hA_bd 0 0 δ δ ht
      have h := variationalSolutionFun_linear hT hM hMT hA_cont hA_bd c 0 δ δ ht
      have h_lhs_eq : c • δ + (0 : ℝ) • δ = c • δ := by simp
      have h_rhs_eq : c • variationalSolutionFun hT hM hMT hA_cont hA_bd δ t
            + (0 : ℝ) • variationalSolutionFun hT hM hMT hA_cont hA_bd δ t
          = c • variationalSolutionFun hT hM hMT hA_cont hA_bd δ t := by simp
      rw [h_lhs_eq] at h
      rw [h_rhs_eq] at h
      exact h }
  refine L.mkContinuous (_root_.Real.exp (M * T)) (fun δ => ?_)
  exact variationalSolutionFun_norm_le hT hM hMT hA_cont hA_bd δ ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.Flow.variationalLinearMapAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.Flow.variationalLinearMapAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.Flow.variationalLinearMapAt ``Submission.DifferentialGeometry.Analysis.ODE.Flow.variationalLinearMapAt

@[simp]
lemma variationalLinearMapAt_apply
    {T M : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (hMT : M * T < 1)
    (hA_cont : ContinuousOn (fun t => fderiv ℝ (f t) (α t)) (_root_.Set.Icc (t₀ - T) (t₀ + T)))
    (hA_bd : ∀ t ∈ _root_.Set.Icc (t₀ - T) (t₀ + T), ‖fderiv ℝ (f t) (α t)‖ ≤ M)
    {t : ℝ} (ht : t ∈ _root_.Set.Icc (t₀ - T) (t₀ + T)) (δ : E) :
    variationalLinearMapAt hT hM hMT hA_cont hA_bd ht δ
      = variationalSolutionFun hT hM hMT hA_cont hA_bd δ t := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.Flow.variationalLinearMapAt_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.Flow.variationalLinearMapAt_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.Flow.variationalLinearMapAt_apply ``Submission.DifferentialGeometry.Analysis.ODE.Flow.variationalLinearMapAt_apply

end LinearMap

end Flow
end ODE
end Analysis
end DifferentialGeometry

end
