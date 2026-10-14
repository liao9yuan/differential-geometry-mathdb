import Submission.DifferentialGeometry.Analysis.Calculus.Cutoff.Basic
import Submission.DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.VariationalODE.BanachIC

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Analysis.ODE
noncomputable section

open _root_.Filter _root_.Function _root_.Metric _root_.Set
open scoped _root_.ContDiff _root_.NNReal _root_.Topology

namespace DifferentialGeometry
namespace Analysis
namespace ODE
namespace Flow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem orbit_unique_on
    {Ω : Set E} (hΩ : IsOpen Ω)
    {v : E → E} (hv : ContDiffOn ℝ 1 v Ω)
    {f g : ℝ → E} {a b t₀ : ℝ} (ht₀ : t₀ ∈ _root_.Set.Ioo a b)
    (hf : ∀ t ∈ _root_.Set.Ioo a b, HasDerivAt f (v (f t)) t)
    (hg : ∀ t ∈ _root_.Set.Ioo a b, HasDerivAt g (v (g t)) t)
    (hfΩ : _root_.Set.MapsTo f (_root_.Set.Ioo a b) Ω)
    (h₀ : f t₀ = g t₀) :
    EqOn f g (_root_.Set.Ioo a b) := by
  set u : Set ℝ := {t | f t = g t} ∩ _root_.Set.Ioo a b with hu
  suffices hsub : _root_.Set.Ioo a b ⊆ u from fun t ht ↦ (hsub ht).1
  apply isPreconnected_Ioo.subset_of_closure_inter_subset (s := _root_.Set.Ioo a b) (u := u) _
    ⟨t₀, ht₀, h₀, ht₀⟩
  · rw [hu, _root_.Set.inter_comm, ← Subtype.image_preimage_val, _root_.Set.inter_comm,
      ← Subtype.image_preimage_val, _root_.Set.image_subset_image_iff Subtype.val_injective,
      _root_.Set.preimage_ofPred_eq]
    intro t ht
    rw [_root_.Set.mem_preimage, ← closure_subtype] at ht
    revert ht t
    apply IsClosed.closure_subset (isClosed_eq _ _)
    · rw [continuous_iff_continuousAt]
      rintro ⟨t, ht⟩
      exact (hf t ht).continuousAt.comp continuousAt_subtype_val
    · rw [continuous_iff_continuousAt]
      rintro ⟨t, ht⟩
      exact (hg t ht).continuousAt.comp continuousAt_subtype_val
  · rw [isOpen_iff_mem_nhds]
    rintro t ⟨hfg, ht⟩
    have htime : _root_.Set.Ioo a b ∈ nhds t := Ioo_mem_nhds ht.1 ht.2
    obtain ⟨K, s, hs, hlip⟩ :=
      (show ContDiffAt ℝ 1 v (f t) from
        hv.contDiffAt (hΩ.mem_nhds (hfΩ ht))).exists_lipschitzOnWith
    have hfmem : f ⁻¹' s ∈ nhds t := (hf t ht).continuousAt.preimage_mem_nhds hs
    have hs' : s ∈ nhds (g t) := by
      rw [← hfg]
      exact hs
    have hgmem : g ⁻¹' s ∈ nhds t := (hg t ht).continuousAt.preimage_mem_nhds hs'
    have hfEventually : ∀ᶠ τ in nhds t, HasDerivAt f (v (f τ)) τ ∧ f τ ∈ s := by
      filter_upwards [htime, hfmem] with τ hτ hτs
      exact ⟨hf τ hτ, hτs⟩
    have hgEventually : ∀ᶠ τ in nhds t, HasDerivAt g (v (g τ)) τ ∧ g τ ∈ s := by
      filter_upwards [htime, hgmem] with τ hτ hτs
      exact ⟨hg τ hτ, hτs⟩
    have heq : f =ᶠ[nhds t] g := ODE_solution_unique_of_eventually
      (Filter.Eventually.of_forall fun _ ↦ hlip)
      hfEventually hgEventually hfg
    exact (heq.and htime).mono fun _ h ↦ ⟨h.1, h.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.Flow.orbit_unique_on then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.Flow.orbit_unique_on"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.Flow.orbit_unique_on ``Submission.DifferentialGeometry.Analysis.ODE.Flow.orbit_unique_on

theorem orbit_unique_smooth
    {v : E → E} (hv : ContDiff ℝ 1 v)
    {f g : ℝ → E} {a b t₀ : ℝ} (ht₀ : t₀ ∈ _root_.Set.Ioo a b)
    (hf : ∀ t ∈ _root_.Set.Ioo a b, HasDerivAt f (v (f t)) t)
    (hg : ∀ t ∈ _root_.Set.Ioo a b, HasDerivAt g (v (g t)) t)
    (h₀ : f t₀ = g t₀) :
    EqOn f g (_root_.Set.Ioo a b) := by
  exact orbit_unique_on isOpen_univ hv.contDiffOn ht₀ hf hg
    (fun _ _ => _root_.Set.mem_univ _) h₀

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.Flow.orbit_unique_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.Flow.orbit_unique_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.Flow.orbit_unique_smooth ``Submission.DifferentialGeometry.Analysis.ODE.Flow.orbit_unique_smooth

section UniformRestart

variable [CompleteSpace E] [FiniteDimensional ℝ E]

omit [CompleteSpace E] in
theorem orbit_unique_Icc
    {v : E → E} (hv : ContDiff ℝ ∞ v)
    {f g : ℝ → E} {a b : ℝ}
    (hf : IsIntegralCurveOn f (fun _ => v) (_root_.Set.Icc a b))
    (hg : IsIntegralCurveOn g (fun _ => v) (_root_.Set.Icc a b))
    (h₀ : f a = g a) :
    EqOn f g (_root_.Set.Icc a b) := by
  by_cases hab : a ≤ b
  · have hfBound : Bornology.IsBounded (f '' _root_.Set.Icc a b) :=
      (isCompact_Icc.image_of_continuousOn hf.continuousOn).isBounded
    have hgBound : Bornology.IsBounded (g '' _root_.Set.Icc a b) :=
      (isCompact_Icc.image_of_continuousOn hg.continuousOn).isBounded
    obtain ⟨Rf, hRf⟩ := hfBound.subset_ball 0
    obtain ⟨Rg, hRg⟩ := hgBound.subset_ball 0
    let R : ℝ := _root_.Max.max (_root_.Max.max Rf Rg) 0 + 1
    have hR : 0 < R := by
      dsimp [R]
      linarith [le_max_right (_root_.Max.max Rf Rg) 0]
    have hfMem : ∀ t ∈ _root_.Set.Ico a b, f t ∈ _root_.Metric.closedBall (0 : E) R := by
      intro t ht
      have hmem := hRf (_root_.Set.mem_image_of_mem f (_root_.Set.Ico_subset_Icc_self ht))
      rw [_root_.Metric.mem_ball] at hmem
      rw [_root_.Metric.mem_closedBall]
      calc
        dist (f t) 0 ≤ Rf := hmem.le
        _ ≤ _root_.Max.max Rf Rg := le_max_left _ _
        _ ≤ _root_.Max.max (_root_.Max.max Rf Rg) 0 := le_max_left _ _
        _ ≤ R := by dsimp [R]; linarith
    have hgMem : ∀ t ∈ _root_.Set.Ico a b, g t ∈ _root_.Metric.closedBall (0 : E) R := by
      intro t ht
      have hmem := hRg (_root_.Set.mem_image_of_mem g (_root_.Set.Ico_subset_Icc_self ht))
      rw [_root_.Metric.mem_ball] at hmem
      rw [_root_.Metric.mem_closedBall]
      calc
        dist (g t) 0 ≤ Rg := hmem.le
        _ ≤ _root_.Max.max Rf Rg := le_max_right _ _
        _ ≤ _root_.Max.max (_root_.Max.max Rf Rg) 0 := le_max_left _ _
        _ ≤ R := by dsimp [R]; linarith
    have hderivCont : ContinuousOn (fun x : E => ‖fderiv ℝ v x‖)
        (_root_.Metric.closedBall (0 : E) R) := by
      exact continuous_norm.comp_continuousOn
        ((hv.contDiffOn.continuousOn_fderiv_of_isOpen isOpen_univ (by simp)).mono
          (_root_.Set.subset_univ _))
    have hballNe : (_root_.Metric.closedBall (0 : E) R).Nonempty :=
      ⟨0, _root_.Metric.mem_closedBall_self hR.le⟩
    obtain ⟨xmax, hxmax, hmax⟩ :=
      (_root_.ProperSpace.isCompact_closedBall (0 : E) R).exists_isMaxOn hballNe hderivCont
    let K : NNReal := ⟨‖fderiv ℝ v xmax‖, norm_nonneg _⟩
    have hvLip : LipschitzOnWith K v (_root_.Metric.closedBall (0 : E) R) := by
      apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le
        (fun x _ => hv.differentiable (by simp) x) ?_ (convex_closedBall _ _)
      intro x hx
      rw [← NNReal.coe_le_coe]
      exact hmax hx
    have hfRight : ∀ t ∈ _root_.Set.Ico a b,
        HasDerivWithinAt f (v (f t)) (_root_.Set.Ici t) t := by
      intro t ht
      exact (hf t (_root_.Set.Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ht)
    have hgRight : ∀ t ∈ _root_.Set.Ico a b,
        HasDerivWithinAt g (v (g t)) (_root_.Set.Ici t) t := by
      intro t ht
      exact (hg t (_root_.Set.Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ht)
    exact ODE_solution_unique_of_mem_Icc_right
      (v := fun _ => v) (s := fun _ => _root_.Metric.closedBall (0 : E) R) (K := K)
      (fun _ _ => hvLip) hf.continuousOn hfRight hfMem
      hg.continuousOn hgRight hgMem h₀
  · rw [_root_.Set.Icc_eq_empty hab]
    exact Set.eqOn_empty f g

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.Flow.orbit_unique_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.Flow.orbit_unique_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.Flow.orbit_unique_Icc ``Submission.DifferentialGeometry.Analysis.ODE.Flow.orbit_unique_Icc

omit [CompleteSpace E] in
theorem orbit_unique_Icc_on
    {Ω : Set E} (hΩ : IsOpen Ω)
    {v : E → E} (hv : ContDiffOn ℝ ∞ v Ω)
    {f g : ℝ → E} {a b : ℝ}
    (hf : IsIntegralCurveOn f (fun _ => v) (_root_.Set.Icc a b))
    (hg : IsIntegralCurveOn g (fun _ => v) (_root_.Set.Icc a b))
    (hfΩ : _root_.Set.MapsTo f (_root_.Set.Icc a b) Ω)
    (hgΩ : _root_.Set.MapsTo g (_root_.Set.Icc a b) Ω)
    (h₀ : f a = g a) :
    EqOn f g (_root_.Set.Icc a b) := by
  let C : Set E := f '' _root_.Set.Icc a b ∪ g '' _root_.Set.Icc a b
  have hC : IsCompact C := by
    exact (isCompact_Icc.image_of_continuousOn hf.continuousOn).union
      (isCompact_Icc.image_of_continuousOn hg.continuousOn)
  have hCΩ : C ⊆ Ω := by
    rintro x (hx | hx)
    · obtain ⟨t, ht, rfl⟩ := hx
      exact hfΩ ht
    · obtain ⟨t, ht, rfl⟩ := hx
      exact hgΩ ht
  obtain ⟨χ, hχ, hχone, hχsupport, _⟩ :=
    DifferentialGeometry.Analysis.exists_bump_one_on hC hΩ hCΩ
  let w : E → E := fun x => χ x • v x
  have hw : ContDiff ℝ ∞ w :=
    DifferentialGeometry.Analysis.contDiff_cutoff_smul hΩ hχ hχsupport hv
  have hfw : IsIntegralCurveOn f (fun _ => w) (_root_.Set.Icc a b) := by
    intro t ht
    have hχf : χ (f t) = 1 := hχone (Or.inl ⟨t, ht, rfl⟩)
    simpa only [w, hχf, one_smul] using hf t ht
  have hgw : IsIntegralCurveOn g (fun _ => w) (_root_.Set.Icc a b) := by
    intro t ht
    have hχg : χ (g t) = 1 := hχone (Or.inr ⟨t, ht, rfl⟩)
    simpa only [w, hχg, one_smul] using hg t ht
  exact orbit_unique_Icc hw hfw hgw h₀

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.Flow.orbit_unique_Icc_on then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.Flow.orbit_unique_Icc_on"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.Flow.orbit_unique_Icc_on ``Submission.DifferentialGeometry.Analysis.ODE.Flow.orbit_unique_Icc_on

theorem exists_uniform_flow
    {v : E → E} (hv : ContDiff ℝ ∞ v) {K : Set E} (hK : IsCompact K) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ K,
      ∃ (U : Set E), IsOpen U ∧ y ∈ U ∧
        ∃ Ψ : E × ℝ → E,
          (∀ z ∈ U, Ψ (z, 0) = z) ∧
          ContDiffOn ℝ ∞ Ψ (U ×ˢ _root_.Set.Ioo (-ε) ε) ∧
          ∀ z ∈ U, ∀ t ∈ _root_.Set.Ioo (-ε) ε,
            HasDerivAt (fun s ↦ Ψ (z, s)) (v (Ψ (z, t))) t := by
  have hvTime : ContDiff ℝ ∞ (_root_.Function.uncurry (fun _ : ℝ ↦ v)) := by
    let h : ContDiff ℝ ∞ (_root_.Function.uncurry (fun _ : ℝ ↦ v)) := hv.comp contDiff_snd
    exact h
  choose r δ hr hδ Ψ hΨ ρ T hρ hT hρr hTδ hΨsm using
    fun y : E ↦
      DifferentialGeometry.Analysis.ODE.exists_isLocalFlow_contDiffOn_top
        (E := E) (f := fun _ : ℝ ↦ v) (t₀ := 0) (x₀ := y) hvTime
  let U : E → Set E := fun y ↦ _root_.Metric.ball y (ρ y)
  have hcover : K ⊆ ⋃ y, U y := by
    intro y _
    exact mem_iUnion.mpr ⟨y, _root_.Metric.mem_ball_self (hρ y)⟩
  obtain ⟨sf, hsf⟩ := hK.elim_finite_subcover U (fun _ ↦ _root_.Metric.isOpen_ball) hcover
  let ε : ℝ := if h : sf.Nonempty then sf.inf' h T else 1
  have hε : 0 < ε := by
    rw [show ε = if h : sf.Nonempty then sf.inf' h T else 1 by rfl]
    split
    · next h => rw [Finset.lt_inf'_iff]; exact fun y _ ↦ hT y
    · exact one_pos
  have hεT : ∀ y ∈ sf, ε ≤ T y := by
    intro y hy
    rw [show ε = if h : sf.Nonempty then sf.inf' h T else 1 by rfl]
    split
    · next h => exact Finset.inf'_le _ hy
    · next h => exact absurd ⟨y, hy⟩ h
  refine ⟨ε, hε, ?_⟩
  intro y hy
  have hymem := hsf hy
  rw [_root_.Set.mem_iUnion₂] at hymem
  obtain ⟨p, hp, hyperbolic⟩ := hymem
  refine ⟨U p, _root_.Metric.isOpen_ball, hyperbolic, Ψ p, ?_, ?_, ?_⟩
  · intro z hz
    have hz' : z ∈ _root_.Metric.closedBall p (r p : ℝ) := by
      rw [_root_.Metric.mem_closedBall]
      exact (mem_ball.mp hz).le.trans (hρr p)
    simpa using (hΨ p).apply_initial z hz'
  · exact (hΨsm p).mono (Set.prod_mono (Subset.rfl) fun t ht ↦
      ⟨by linarith [ht.1, hεT p hp], by linarith [ht.2, hεT p hp]⟩)
  · intro z hz t ht
    have hz' : z ∈ _root_.Metric.closedBall p (r p : ℝ) := by
      rw [_root_.Metric.mem_closedBall]
      exact (mem_ball.mp hz).le.trans (hρr p)
    have ht' : t ∈ _root_.Set.Ioo ((0 : ℝ) - δ p) (0 + δ p) :=
      ⟨by linarith [ht.1, hεT p hp, hTδ p],
        by linarith [ht.2, hεT p hp, hTδ p]⟩
    simpa using ((hΨ p).hasDerivWithinAt z hz' t (_root_.Set.Ioo_subset_Icc_self ht')).hasDerivAt
      (Icc_mem_nhds ht'.1 ht'.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.Flow.exists_uniform_flow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.Flow.exists_uniform_flow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.Flow.exists_uniform_flow ``Submission.DifferentialGeometry.Analysis.ODE.Flow.exists_uniform_flow

theorem exists_flow_on
    {Ω : Set E} (hΩ : IsOpen Ω)
    {v : E → E} (hv : ContDiffOn ℝ ∞ v Ω)
    {K : Set E} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ K,
      ∃ (U : Set E), IsOpen U ∧ y ∈ U ∧
        ∃ Ψ : E × ℝ → E,
          (∀ z ∈ U, Ψ (z, 0) = z) ∧
          ContDiffOn ℝ ∞ Ψ (U ×ˢ _root_.Set.Ioo (-ε) ε) ∧
          (∀ z ∈ U, ∀ t ∈ _root_.Set.Ioo (-ε) ε,
            HasDerivAt (fun s ↦ Ψ (z, s)) (v (Ψ (z, t))) t) ∧
          MapsTo Ψ (U ×ˢ _root_.Set.Ioo (-ε) ε) Ω := by
  obtain ⟨L, hL, hKL, hLΩ⟩ := exists_compact_between hK hΩ hKΩ
  obtain ⟨χ, hχ, hχone, hχsupport, _⟩ :=
    DifferentialGeometry.Analysis.exists_bump_one_on hL hΩ hLΩ
  let w : E → E := fun x => χ x • v x
  have hw : ContDiff ℝ ∞ w :=
    DifferentialGeometry.Analysis.contDiff_cutoff_smul hΩ hχ hχsupport hv
  obtain ⟨ε₀, hε₀, hlocal⟩ := exists_uniform_flow hw hK
  choose U₀ hU₀ hyU₀ Ψ hΨ₀ hΨsm hΨderiv using
    fun y : K ↦ hlocal y y.2
  have hpre : ∀ y : K, Ψ y ⁻¹' interior L ∈ 𝓝 ((y : E), (0 : ℝ)) := by
    intro y
    have hp : ((y : E), (0 : ℝ)) ∈ U₀ y ×ˢ _root_.Set.Ioo (-ε₀) ε₀ := by
      exact ⟨hyU₀ y, ⟨by linarith, by linarith⟩⟩
    have hΨat : ContDiffAt ℝ ∞ (Ψ y) ((y : E), (0 : ℝ)) :=
      (hΨsm y _ hp).contDiffAt ((hU₀ y).prod isOpen_Ioo |>.mem_nhds hp)
    have hyL : (y : E) ∈ interior L := hKL y.2
    have hΨyL : Ψ y ((y : E), (0 : ℝ)) ∈ interior L := by
      rw [hΨ₀ y (y : E) (hyU₀ y)]
      exact hyL
    exact hΨat.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hΨyL)
  choose δ hδ hball using fun y : K ↦ Metric.mem_nhds_iff.mp (hpre y)
  let τ : K → ℝ := fun y => _root_.Min.min (δ y / 2) (ε₀ / 2)
  have hτ : ∀ y : K, 0 < τ y := by
    intro y
    exact lt_min (half_pos (hδ y)) (half_pos hε₀)
  let U : K → Set E := fun y => U₀ y ∩ _root_.Metric.ball y (τ y)
  have hU : ∀ y : K, IsOpen (U y) := fun y => (hU₀ y).inter _root_.Metric.isOpen_ball
  have hcover : K ⊆ ⋃ y : K, U y := by
    intro y hy
    exact mem_iUnion.mpr ⟨⟨y, hy⟩, ⟨hyU₀ ⟨y, hy⟩, _root_.Metric.mem_ball_self (hτ ⟨y, hy⟩)⟩⟩
  obtain ⟨sf, hsf⟩ := hK.elim_finite_subcover U hU hcover
  let ε : ℝ := if h : sf.Nonempty then sf.inf' h τ else 1
  have hε : 0 < ε := by
    rw [show ε = if h : sf.Nonempty then sf.inf' h τ else 1 by rfl]
    split
    · next h => rw [Finset.lt_inf'_iff]; exact fun y _ => hτ y
    · exact one_pos
  have hετ : ∀ y ∈ sf, ε ≤ τ y := by
    intro y hy
    rw [show ε = if h : sf.Nonempty then sf.inf' h τ else 1 by rfl]
    split
    · next h => exact Finset.inf'_le _ hy
    · next h => exact absurd ⟨y, hy⟩ h
  refine ⟨ε, hε, ?_⟩
  intro y hy
  have hymem := hsf hy
  rw [_root_.Set.mem_iUnion₂] at hymem
  obtain ⟨p, hp, hyperbolic⟩ := hymem
  refine ⟨U p, hU p, hyperbolic, Ψ p, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact hΨ₀ p z hz.1
  · apply (hΨsm p).mono
    rintro ⟨z, t⟩ ⟨hz, ht⟩
    refine ⟨hz.1, ?_⟩
    have hεε₀ : ε < ε₀ :=
      (hετ p hp).trans_lt ((min_le_right _ _).trans_lt (half_lt_self hε₀))
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · intro z hz t ht
    have hεε₀ : ε < ε₀ :=
      (hετ p hp).trans_lt ((min_le_right _ _).trans_lt (half_lt_self hε₀))
    have ht₀ : t ∈ _root_.Set.Ioo (-ε₀) ε₀ := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hpair : ((z, t) : E × ℝ) ∈ _root_.Metric.ball ((p : E), (0 : ℝ)) (δ p) := by
      rw [_root_.Metric.mem_ball, Prod.dist_eq]
      apply max_lt
      · exact (mem_ball.mp hz.2).trans_le (min_le_left _ _ |>.trans (half_le_self (hδ p).le))
      · rw [Real.dist_eq, sub_zero]
        exact (abs_lt.mpr ht).trans_le
          ((hετ p hp).trans (min_le_left _ _ |>.trans (half_le_self (hδ p).le)))
    have hΨL : Ψ p (z, t) ∈ interior L := hball p hpair
    have hχΨ : χ (Ψ p (z, t)) = 1 := hχone (interior_subset hΨL)
    simpa only [w, hχΨ, one_smul] using hΨderiv p z hz.1 t ht₀
  · rintro ⟨z, t⟩ ⟨hz, ht⟩
    have hpair : ((z, t) : E × ℝ) ∈ _root_.Metric.ball ((p : E), (0 : ℝ)) (δ p) := by
      rw [_root_.Metric.mem_ball, Prod.dist_eq]
      apply max_lt
      · exact (mem_ball.mp hz.2).trans_le (min_le_left _ _ |>.trans (half_le_self (hδ p).le))
      · rw [Real.dist_eq, sub_zero]
        exact (abs_lt.mpr ht).trans_le
          ((hετ p hp).trans (min_le_left _ _ |>.trans (half_le_self (hδ p).le)))
    exact hLΩ (interior_subset (hball p hpair))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.Flow.exists_flow_on then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.Flow.exists_flow_on"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.Flow.exists_flow_on ``Submission.DifferentialGeometry.Analysis.ODE.Flow.exists_flow_on

theorem flow_slice_right_on
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {Ω : Set E} (hΩ : IsOpen Ω)
    {v : E → E} (hv : ContDiffOn ℝ ∞ v Ω)
    {A : Set P} (hA : IsOpen A)
    {a b : ℝ}
    {a₀ : P → E} (ha₀ : ContDiffOn ℝ ∞ a₀ A)
    {γ : P → ℝ → E}
    (hγ : ∀ p ∈ A,
      γ p a = a₀ p ∧
      IsIntegralCurveOn (γ p) (fun _ => v) (_root_.Set.Icc a b))
    (hstay : ∀ p ∈ A, _root_.Set.MapsTo (γ p) (_root_.Set.Icc a b) Ω) :
    ∀ t ∈ _root_.Set.Icc a b, ContDiffOn ℝ ∞ (fun p => γ p t) A := by
  intro target htarget x hx
  let K : Set E := γ x '' _root_.Set.Icc a b
  have hK : IsCompact K :=
    isCompact_Icc.image_of_continuousOn ((hγ x hx).2.continuousOn)
  have hKΩ : K ⊆ Ω := by
    rintro y ⟨t, ht, rfl⟩
    exact hstay x hx ht
  obtain ⟨ε, hε, hlocal⟩ := exists_flow_on hΩ hv hK hKΩ
  have hstep : ∀ s₀ ∈ _root_.Set.Icc a b,
      ContDiffAt ℝ ∞ (fun p => γ p s₀) x →
      ∀ s ∈ _root_.Set.Icc a b, s₀ ≤ s → s - s₀ < ε →
        ContDiffAt ℝ ∞ (fun p => γ p s) x := by
    intro s₀ hs₀ hsmooth s hs hs₀s hss₀
    have hyK : γ x s₀ ∈ K := ⟨s₀, hs₀, rfl⟩
    obtain ⟨U, hU, hyU, Ψ, hΨ0, hΨsm, hΨderiv, hΨΩ⟩ :=
      hlocal (γ x s₀) hyK
    have hτ : s - s₀ ∈ _root_.Set.Ioo (-ε) ε := by
      constructor <;> linarith
    have hp_mem : (γ x s₀, s - s₀) ∈ U ×ˢ _root_.Set.Ioo (-ε) ε := ⟨hyU, hτ⟩
    have hΨat : ContDiffAt ℝ ∞ Ψ (γ x s₀, s - s₀) :=
      (hΨsm _ hp_mem).contDiffAt ((hU.prod isOpen_Ioo).mem_nhds hp_mem)
    have hpair : ContDiffAt ℝ ∞ (fun p => (γ p s₀, s - s₀)) x :=
      hsmooth.prodMk contDiffAt_const
    have hcand : ContDiffAt ℝ ∞ (fun p => Ψ (γ p s₀, s - s₀)) x :=
      hΨat.comp x hpair
    have hstate : (fun p => γ p s₀) ⁻¹' U ∈ nhds x :=
      hsmooth.continuousAt.preimage_mem_nhds (hU.mem_nhds hyU)
    have heq : (fun p => Ψ (γ p s₀, s - s₀)) =ᶠ[nhds x]
        (fun p => γ p s) := by
      filter_upwards [hA.mem_nhds hx, hstate] with p hpA hpState
      let left : ℝ → E := fun t => Ψ (γ p s₀, t - s₀)
      have hleft : IsIntegralCurveOn left (fun _ => v) (_root_.Set.Icc s₀ s) := by
        intro t ht
        have htτ : t - s₀ ∈ _root_.Set.Ioo (-ε) ε := by
          constructor
          · linarith [ht.1]
          · linarith [ht.2]
        have houter := hΨderiv (γ p s₀) hpState (t - s₀) htτ
        simpa only [left] using (houter.comp_sub_const t s₀).hasDerivWithinAt
      have hright : IsIntegralCurveOn (γ p) (fun _ => v) (_root_.Set.Icc s₀ s) :=
        (hγ p hpA).2.mono fun t ht =>
          ⟨hs₀.1.trans ht.1, ht.2.trans hs.2⟩
      have hleftΩ : _root_.Set.MapsTo left (_root_.Set.Icc s₀ s) Ω := by
        intro t ht
        apply hΨΩ
        exact ⟨hpState, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
      have hrightΩ : _root_.Set.MapsTo (γ p) (_root_.Set.Icc s₀ s) Ω := by
        intro t ht
        exact hstay p hpA ⟨hs₀.1.trans ht.1, ht.2.trans hs.2⟩
      have hstart : left s₀ = γ p s₀ := by
        simpa only [left, sub_self] using hΨ0 (γ p s₀) hpState
      exact orbit_unique_Icc_on hΩ hv hleft hright hleftΩ hrightΩ hstart
        ⟨hs₀s, le_rfl⟩
    exact hcand.congr_of_eventuallyEq heq.symm
  have hbase : ContDiffAt ℝ ∞ (fun p => γ p a) x := by
    apply (ha₀.contDiffAt (hA.mem_nhds hx)).congr_of_eventuallyEq
    filter_upwards [hA.mem_nhds hx] with p hp
    exact (hγ p hp).1
  obtain ⟨N, hN⟩ := exists_nat_gt ((target - a) / ε)
  have hratio : 0 ≤ (target - a) / ε :=
    div_nonneg (sub_nonneg.mpr htarget.1) hε.le
  have hNpos : 0 < N := by
    exact_mod_cast (hratio.trans_lt hN)
  let d : ℝ := (target - a) / N
  have hd : 0 ≤ d := by
    dsimp [d]
    exact div_nonneg (sub_nonneg.mpr htarget.1) (Nat.cast_nonneg N)
  have hNd : (N : ℝ) * d = target - a := by
    dsimp [d]
    field_simp
  have hdε : d < ε := by
    have hprod : target - a < (N : ℝ) * ε :=
      (div_lt_iff₀ hε).mp hN
    rw [show d = (target - a) / (N : ℝ) by rfl,
      div_lt_iff₀ (by exact_mod_cast hNpos)]
    nlinarith
  let grid : ℕ → ℝ := fun i => a + (i : ℝ) * d
  have hgrid_mem : ∀ i ≤ N, grid i ∈ _root_.Set.Icc a b := by
    intro i hi
    have hi' : (i : ℝ) ≤ (N : ℝ) := by exact_mod_cast hi
    have hmul_nonneg : 0 ≤ (i : ℝ) * d := mul_nonneg (Nat.cast_nonneg i) hd
    have hmul_le : (i : ℝ) * d ≤ (N : ℝ) * d :=
      mul_le_mul_of_nonneg_right hi' hd
    constructor
    · dsimp [grid]
      linarith
    · dsimp [grid]
      nlinarith [hNd, hmul_le, htarget.2]
  have hgrid_zero : grid 0 = a := by simp [grid]
  have hgrid_N : grid N = target := by
    dsimp [grid]
    nlinarith [hNd]
  have hsmooth_grid : ∀ i : ℕ, i ≤ N →
      ContDiffAt ℝ ∞ (fun p => γ p (grid i)) x := by
    intro i
    induction i with
    | zero =>
        intro _
        simpa only [hgrid_zero] using hbase
    | succ i ih =>
        intro hi
        have hiN : i ≤ N := (Nat.le_succ i).trans hi
        have horder : grid i ≤ grid (i + 1) := by
          dsimp [grid]
          push_cast
          nlinarith
        have hdiff : grid (i + 1) - grid i < ε := by
          have heq : grid (i + 1) - grid i = d := by
            dsimp [grid]
            push_cast
            ring
          rw [heq]
          exact hdε
        exact hstep (grid i) (hgrid_mem i hiN) (ih hiN)
          (grid (i + 1)) (hgrid_mem (i + 1) hi) horder hdiff
  have htargetSmooth := hsmooth_grid N le_rfl
  rw [hgrid_N] at htargetSmooth
  exact htargetSmooth.contDiffWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.Flow.flow_slice_right_on then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.Flow.flow_slice_right_on"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.Flow.flow_slice_right_on ``Submission.DifferentialGeometry.Analysis.ODE.Flow.flow_slice_right_on

theorem flow_joint_right_on
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {Ω : Set E} (hΩ : IsOpen Ω)
    {v : E → E} (hv : ContDiffOn ℝ ∞ v Ω)
    {A : Set P} (hA : IsOpen A)
    {a b : ℝ}
    {a₀ : P → E} (ha₀ : ContDiffOn ℝ ∞ a₀ A)
    {γ : P → ℝ → E}
    (hγ : ∀ p ∈ A,
      γ p a = a₀ p ∧
      IsIntegralCurveOn (γ p) (fun _ => v) (_root_.Set.Icc a b))
    (hstay : ∀ p ∈ A, _root_.Set.MapsTo (γ p) (_root_.Set.Icc a b) Ω) :
    ContDiffOn ℝ ∞ (_root_.Function.uncurry γ) (A ×ˢ _root_.Set.Icc a b) := by
  rintro ⟨x, t⟩ ⟨hx, ht⟩
  let K : Set E := γ x '' _root_.Set.Icc a b
  have hK : IsCompact K :=
    isCompact_Icc.image_of_continuousOn ((hγ x hx).2.continuousOn)
  have hKΩ : K ⊆ Ω := by
    rintro y ⟨s, hs, rfl⟩
    exact hstay x hx hs
  obtain ⟨ε, hε, hlocal⟩ := exists_flow_on hΩ hv hK hKΩ
  let s₀ : ℝ := _root_.Max.max a (t - ε / 2)
  have hs₀a : a ≤ s₀ := le_max_left _ _
  have hs₀t : s₀ ≤ t := by
    exact max_le ht.1 (sub_le_self _ (half_pos hε).le)
  have hs₀ : s₀ ∈ _root_.Set.Icc a b := ⟨hs₀a, hs₀t.trans ht.2⟩
  have htτ : t - s₀ ∈ _root_.Set.Ioo (-ε) ε := by
    constructor
    · linarith
    · have hs₀lower : t - ε / 2 ≤ s₀ := le_max_right _ _
      linarith
  have hyK : γ x s₀ ∈ K := ⟨s₀, hs₀, rfl⟩
  obtain ⟨U, hU, hyU, Ψ, hΨ0, hΨsm, hΨderiv, hΨΩ⟩ :=
    hlocal (γ x s₀) hyK
  have hp_mem : (γ x s₀, t - s₀) ∈ U ×ˢ _root_.Set.Ioo (-ε) ε := ⟨hyU, htτ⟩
  have hΨat : ContDiffAt ℝ ∞ Ψ (γ x s₀, t - s₀) :=
    (hΨsm _ hp_mem).contDiffAt ((hU.prod isOpen_Ioo).mem_nhds hp_mem)
  have hslice := flow_slice_right_on hΩ hv hA ha₀ hγ hstay s₀ hs₀
  have hsliceAt : ContDiffAt ℝ ∞ (fun p => γ p s₀) x :=
    hslice.contDiffAt (hA.mem_nhds hx)
  have hpair : ContDiffAt ℝ ∞
      (fun q : P × ℝ => (γ q.1 s₀, q.2 - s₀)) (x, t) :=
    (hsliceAt.comp (x, t) contDiffAt_fst).prodMk
      (contDiffAt_snd.sub contDiffAt_const)
  have hcand : ContDiffAt ℝ ∞
      (fun q : P × ℝ => Ψ (γ q.1 s₀, q.2 - s₀)) (x, t) :=
    hΨat.comp (x, t) hpair
  have hstate : (fun p => γ p s₀) ⁻¹' U ∈ 𝓝 x :=
    hsliceAt.continuousAt.preimage_mem_nhds (hU.mem_nhds hyU)
  have htime : _root_.Set.Ioo (t - ε / 4) (t + ε / 4) ∈ 𝓝 t :=
    isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
  have hbox :
      ((A ∩ (fun p => γ p s₀) ⁻¹' U) ×ˢ _root_.Set.Ioo (t - ε / 4) (t + ε / 4)) ∈
        𝓝 (x, t) := by
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod (Filter.inter_mem (hA.mem_nhds hx) hstate) htime
  have heq : (fun q : P × ℝ => Ψ (γ q.1 s₀, q.2 - s₀)) =ᶠ[
      𝓝[A ×ˢ _root_.Set.Icc a b] (x, t)] _root_.Function.uncurry γ := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds hbox, self_mem_nhdsWithin]
      with q hqbox hqdom
    rcases q with ⟨p, s⟩
    rcases hqbox with ⟨⟨hpA, hpU⟩, hswin⟩
    rcases hqdom with ⟨_, hs⟩
    have hs₀s : s₀ ≤ s := by
      apply max_le hs.1
      linarith [hswin.1]
    have hsτ : s - s₀ ∈ _root_.Set.Ioo (-ε) ε := by
      constructor
      · linarith
      · have hs₀lower : t - ε / 2 ≤ s₀ := le_max_right _ _
        linarith [hswin.2]
    let left : ℝ → E := fun u => Ψ (γ p s₀, u - s₀)
    have hleft : IsIntegralCurveOn left (fun _ => v) (_root_.Set.Icc s₀ s) := by
      intro u hu
      have huτ : u - s₀ ∈ _root_.Set.Ioo (-ε) ε := by
        constructor
        · linarith [hu.1]
        · linarith [hu.2, hsτ.2]
      have houter := hΨderiv (γ p s₀) hpU (u - s₀) huτ
      simpa only [left] using (houter.comp_sub_const u s₀).hasDerivWithinAt
    have hright : IsIntegralCurveOn (γ p) (fun _ => v) (_root_.Set.Icc s₀ s) :=
      (hγ p hpA).2.mono fun u hu => ⟨hs₀.1.trans hu.1, hu.2.trans hs.2⟩
    have hleftΩ : _root_.Set.MapsTo left (_root_.Set.Icc s₀ s) Ω := by
      intro u hu
      apply hΨΩ
      exact ⟨hpU, ⟨by linarith [hu.1], by linarith [hu.2, hsτ.2]⟩⟩
    have hrightΩ : _root_.Set.MapsTo (γ p) (_root_.Set.Icc s₀ s) Ω := by
      intro u hu
      exact hstay p hpA ⟨hs₀.1.trans hu.1, hu.2.trans hs.2⟩
    have hstart : left s₀ = γ p s₀ := by
      simpa only [left, sub_self] using hΨ0 (γ p s₀) hpU
    exact orbit_unique_Icc_on hΩ hv hleft hright hleftΩ hrightΩ hstart
      ⟨hs₀s, le_rfl⟩
  exact hcand.contDiffWithinAt.congr_of_eventuallyEq_of_mem heq.symm ⟨hx, ht⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.Flow.flow_joint_right_on then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.Flow.flow_joint_right_on"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.Flow.flow_joint_right_on ``Submission.DifferentialGeometry.Analysis.ODE.Flow.flow_joint_right_on

theorem flow_slice_right
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {v : E → E} (hv : ContDiff ℝ ∞ v)
    {A : Set P} (hA : IsOpen A)
    {a b : ℝ}
    {a₀ : P → E} (ha₀ : ContDiffOn ℝ ∞ a₀ A)
    {γ : P → ℝ → E}
    (hγ : ∀ p ∈ A,
      γ p a = a₀ p ∧
      IsIntegralCurveOn (γ p) (fun _ => v) (_root_.Set.Icc a b)) :
    ∀ t ∈ _root_.Set.Icc a b, ContDiffOn ℝ ∞ (fun p => γ p t) A := by
  exact flow_slice_right_on isOpen_univ hv.contDiffOn hA ha₀ hγ
    (fun _ _ _ _ => _root_.Set.mem_univ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.Flow.flow_slice_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.Flow.flow_slice_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.Flow.flow_slice_right ``Submission.DifferentialGeometry.Analysis.ODE.Flow.flow_slice_right

theorem ode_slice_right_on
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {J : Set ℝ} (hJ : IsOpen J)
    {V : Set E} (hV : IsOpen V)
    {v : ℝ → E → E}
    (hv : ContDiffOn ℝ ∞ (_root_.Function.uncurry v) (J ×ˢ V))
    {A : Set P} (hA : IsOpen A)
    {a b : ℝ}
    (hI : _root_.Set.Icc a b ⊆ J)
    {a₀ : P → E} (ha₀ : ContDiffOn ℝ ∞ a₀ A)
    {γ : P → ℝ → E}
    (hγ : ∀ p ∈ A,
      γ p a = a₀ p ∧
      IsIntegralCurveOn (γ p) v (_root_.Set.Icc a b))
    (hstay : ∀ p ∈ A, _root_.Set.MapsTo (γ p) (_root_.Set.Icc a b) V) :
    ∀ t ∈ _root_.Set.Icc a b, ContDiffOn ℝ ∞ (fun p => γ p t) A := by
  let w : ℝ × E → ℝ × E := fun q => (1, v q.1 q.2)
  have hw : ContDiffOn ℝ ∞ w (J ×ˢ V) :=
    contDiffOn_const.prodMk hv
  let aAug : P → ℝ × E := fun p => (a, a₀ p)
  have haAug : ContDiffOn ℝ ∞ aAug A :=
    contDiffOn_const.prodMk ha₀
  let γAug : P → ℝ → ℝ × E := fun p t => (t, γ p t)
  have hγAug : ∀ p ∈ A,
      γAug p a = aAug p ∧
      IsIntegralCurveOn (γAug p) (fun _ => w) (_root_.Set.Icc a b) := by
    intro p hp
    constructor
    · simp only [γAug, aAug, (hγ p hp).1]
    · intro t ht
      have htime : HasDerivWithinAt (fun s : ℝ => s) 1 (_root_.Set.Icc a b) t :=
        hasDerivAt_id t |>.hasDerivWithinAt
      have hstate := (hγ p hp).2 t ht
      simpa only [γAug, w] using htime.prodMk hstate
  have hstayAug : ∀ p ∈ A, _root_.Set.MapsTo (γAug p) (_root_.Set.Icc a b) (J ×ˢ V) := by
    intro p hp t ht
    exact ⟨hI ht, hstay p hp ht⟩
  intro t ht
  exact (flow_slice_right_on (E := ℝ × E) (hJ.prod hV) hw hA haAug hγAug
    hstayAug t ht).snd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.Flow.ode_slice_right_on then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.Flow.ode_slice_right_on"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.Flow.ode_slice_right_on ``Submission.DifferentialGeometry.Analysis.ODE.Flow.ode_slice_right_on

theorem contDiffOn_solutionFamily_of_stays
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {J : Set ℝ} (hJ : IsOpen J)
    {V : Set E} (hV : IsOpen V)
    {v : ℝ → E → E}
    (hv : ContDiffOn ℝ ∞ (_root_.Function.uncurry v) (J ×ˢ V))
    {A : Set P} (hA : IsOpen A)
    {a b : ℝ} (hI : _root_.Set.Icc a b ⊆ J)
    {a₀ : P → E} (ha₀ : ContDiffOn ℝ ∞ a₀ A)
    {γ : P → ℝ → E}
    (hγ : ∀ p ∈ A,
      γ p a = a₀ p ∧ IsIntegralCurveOn (γ p) v (_root_.Set.Icc a b))
    (hstay : ∀ p ∈ A, _root_.Set.MapsTo (γ p) (_root_.Set.Icc a b) V) :
    ContDiffOn ℝ ∞ (_root_.Function.uncurry γ) (A ×ˢ _root_.Set.Icc a b) := by
  let w : ℝ × E → ℝ × E := fun q => (1, v q.1 q.2)
  have hw : ContDiffOn ℝ ∞ w (J ×ˢ V) :=
    contDiffOn_const.prodMk hv
  let aAug : P → ℝ × E := fun p => (a, a₀ p)
  have haAug : ContDiffOn ℝ ∞ aAug A :=
    contDiffOn_const.prodMk ha₀
  let γAug : P → ℝ → ℝ × E := fun p t => (t, γ p t)
  have hγAug : ∀ p ∈ A,
      γAug p a = aAug p ∧
      IsIntegralCurveOn (γAug p) (fun _ => w) (_root_.Set.Icc a b) := by
    intro p hp
    constructor
    · simp only [γAug, aAug, (hγ p hp).1]
    · intro t ht
      have htime : HasDerivWithinAt (fun s : ℝ => s) 1 (_root_.Set.Icc a b) t :=
        (hasDerivAt_id t).hasDerivWithinAt
      have hstate := (hγ p hp).2 t ht
      simpa only [γAug, w] using htime.prodMk hstate
  have hstayAug : ∀ p ∈ A, _root_.Set.MapsTo (γAug p) (_root_.Set.Icc a b) (J ×ˢ V) := by
    intro p hp t ht
    exact ⟨hI ht, hstay p hp ht⟩
  have haug := flow_joint_right_on (E := ℝ × E) (hJ.prod hV) hw hA haAug
    hγAug hstayAug
  let h : ContDiffOn ℝ ∞ (_root_.Function.uncurry γ) (A ×ˢ _root_.Set.Icc a b) := haug.snd
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.Flow.contDiffOn_solutionFamily_of_stays then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.Flow.contDiffOn_solutionFamily_of_stays"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.Flow.contDiffOn_solutionFamily_of_stays ``Submission.DifferentialGeometry.Analysis.ODE.Flow.contDiffOn_solutionFamily_of_stays

theorem ode_slice_right
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {v : ℝ → E → E}
    (hv : ContDiff ℝ ∞ (_root_.Function.uncurry v))
    {A : Set P} (hA : IsOpen A)
    {a b : ℝ}
    {a₀ : P → E} (ha₀ : ContDiffOn ℝ ∞ a₀ A)
    {γ : P → ℝ → E}
    (hγ : ∀ p ∈ A,
      γ p a = a₀ p ∧
      IsIntegralCurveOn (γ p) v (_root_.Set.Icc a b)) :
    ∀ t ∈ _root_.Set.Icc a b, ContDiffOn ℝ ∞ (fun p => γ p t) A := by
  exact ode_slice_right_on isOpen_univ isOpen_univ hv.contDiffOn hA
    (_root_.Set.subset_univ _) ha₀ hγ (fun _ _ _ _ => _root_.Set.mem_univ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.Flow.ode_slice_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.Flow.ode_slice_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.Flow.ode_slice_right ``Submission.DifferentialGeometry.Analysis.ODE.Flow.ode_slice_right

theorem flow_slice_smooth
    {v : E → E} (hv : ContDiff ℝ ∞ v)
    {D : Set E} (hD : IsOpen D) {a b t₀ : ℝ} (ht₀ : t₀ ∈ _root_.Set.Ioo a b)
    {F : E → ℝ → E}
    (hinit : ∀ x ∈ D, F x t₀ = x)
    (hcont : ∀ x ∈ D, ContinuousOn (F x) (_root_.Set.Icc a b))
    (hderiv : ∀ x ∈ D, ∀ t ∈ _root_.Set.Ioo a b, HasDerivAt (F x) (v (F x t)) t) :
    ∀ t ∈ _root_.Set.Ioo a b, ContDiffOn ℝ ∞ (fun x ↦ F x t) D := by
  intro target htarget x hx
  let K : Set E := F x '' _root_.Set.Icc a b
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn (hcont x hx)
  obtain ⟨ε, hε, hlocal⟩ := exists_uniform_flow hv hK
  have hstep : ∀ s₀ ∈ _root_.Set.Ioo a b,
      ContDiffAt ℝ ∞ (fun y ↦ F y s₀) x →
      ∀ s ∈ _root_.Set.Ioo a b, |s - s₀| < ε →
        ContDiffAt ℝ ∞ (fun y ↦ F y s) x := by
    intro s₀ hs₀ hsmooth s hs hss₀
    have hyK : F x s₀ ∈ K :=
      ⟨s₀, ⟨le_of_lt hs₀.1, le_of_lt hs₀.2⟩, rfl⟩
    obtain ⟨U, hU, hyU, Ψ, hΨ0, hΨsm, hΨderiv⟩ := hlocal (F x s₀) hyK
    have hτ : s - s₀ ∈ _root_.Set.Ioo (-ε) ε := by
      rw [_root_.Set.mem_Ioo, ← abs_lt]
      exact hss₀
    have hp_mem : (F x s₀, s - s₀) ∈ U ×ˢ _root_.Set.Ioo (-ε) ε := ⟨hyU, hτ⟩
    have hΨat : ContDiffAt ℝ ∞ Ψ (F x s₀, s - s₀) :=
      (hΨsm _ hp_mem).contDiffAt ((hU.prod isOpen_Ioo).mem_nhds hp_mem)
    have hpair : ContDiffAt ℝ ∞ (fun y ↦ (F y s₀, s - s₀)) x :=
      hsmooth.prodMk contDiffAt_const
    have hcand : ContDiffAt ℝ ∞ (fun y ↦ Ψ (F y s₀, s - s₀)) x :=
      hΨat.comp x hpair
    have hstate : (fun y ↦ F y s₀) ⁻¹' U ∈ nhds x :=
      hsmooth.continuousAt.preimage_mem_nhds (hU.mem_nhds hyU)
    have heq : (fun y ↦ Ψ (F y s₀, s - s₀)) =ᶠ[nhds x] (fun y ↦ F y s) := by
      filter_upwards [hD.mem_nhds hx, hstate] with y hyD hyState
      let left : ℝ → E := fun t ↦ Ψ (F y s₀, t - s₀)
      let lo : ℝ := _root_.Max.max a (s₀ - ε)
      let hi : ℝ := _root_.Min.min b (s₀ + ε)
      have hs₀J : s₀ ∈ _root_.Set.Ioo lo hi := by
        dsimp only [lo, hi]
        exact ⟨max_lt hs₀.1 (sub_lt_self _ hε),
          lt_min hs₀.2 (lt_add_of_pos_right _ hε)⟩
      have hsJ : s ∈ _root_.Set.Ioo lo hi := by
        rw [abs_lt] at hss₀
        dsimp only [lo, hi]
        exact ⟨max_lt hs.1 (by linarith [hss₀.1]),
          lt_min hs.2 (by linarith [hss₀.2])⟩
      have hleft : ∀ t ∈ _root_.Set.Ioo lo hi, HasDerivAt left (v (left t)) t := by
        intro t ht
        have htτ : t - s₀ ∈ _root_.Set.Ioo (-ε) ε := by
          have htleft : s₀ - ε < t :=
            lt_of_le_of_lt (le_max_right a (s₀ - ε)) ht.1
          have htright : t < s₀ + ε :=
            lt_of_lt_of_le ht.2 (min_le_right b (s₀ + ε))
          constructor <;> linarith
        have houter := hΨderiv (F y s₀) hyState (t - s₀) htτ
        simpa only [left] using houter.comp_sub_const t s₀
      have hright : ∀ t ∈ _root_.Set.Ioo lo hi, HasDerivAt (F y) (v (F y t)) t := by
        intro t ht
        exact hderiv y hyD t ⟨lt_of_le_of_lt (le_max_left _ _) ht.1,
          lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
      have hstart : left s₀ = F y s₀ := by
        simpa only [left, sub_self] using hΨ0 (F y s₀) hyState
      exact orbit_unique_smooth (hv.of_le (by simp)) hs₀J hleft hright hstart hsJ
    exact hcand.congr_of_eventuallyEq heq.symm
  let good : Set ℝ :=
    {s | ContDiffAt ℝ ∞ (fun y ↦ F y s) x} ∩ _root_.Set.Ioo a b
  have hgood_open : IsOpen good := by
    rw [isOpen_iff_mem_nhds]
    rintro s₀ ⟨hsmooth, hs₀⟩
    change ContDiffAt ℝ ∞ (fun y ↦ F y s₀) x at hsmooth
    have hwin : _root_.Set.Ioo (s₀ - ε) (s₀ + ε) ∩ _root_.Set.Ioo a b ∈ nhds s₀ :=
      _root_.Filter.inter_mem (Ioo_mem_nhds (sub_lt_self _ hε) (lt_add_of_pos_right _ hε))
        (Ioo_mem_nhds hs₀.1 hs₀.2)
    apply _root_.Filter.mem_of_superset hwin
    rintro s ⟨hswin, hs⟩
    refine ⟨hstep s₀ hs₀ hsmooth s hs ?_, hs⟩
    rw [abs_lt]
    constructor <;> linarith [hswin.1, hswin.2]
  have ht₀_smooth : ContDiffAt ℝ ∞ (fun y ↦ F y t₀) x := by
    apply contDiffAt_id.congr_of_eventuallyEq
    filter_upwards [hD.mem_nhds hx] with y hy
    exact hinit y hy
  have ht₀_good : t₀ ∈ good := ⟨ht₀_smooth, ht₀⟩
  have hgood_closed : closure good ∩ _root_.Set.Ioo a b ⊆ good := by
    rintro sstar ⟨hsstar_cl, hsstar⟩
    have hnhd : _root_.Set.Ioo (sstar - ε) (sstar + ε) ∩ _root_.Set.Ioo a b ∈ nhds sstar :=
      _root_.Filter.inter_mem (Ioo_mem_nhds (sub_lt_self _ hε) (lt_add_of_pos_right _ hε))
        (Ioo_mem_nhds hsstar.1 hsstar.2)
    obtain ⟨sn, ⟨hsn_ball, _⟩, hsn_smooth, hsn⟩ :=
      mem_closure_iff_nhds.mp hsstar_cl _ hnhd
    change ContDiffAt ℝ ∞ (fun y ↦ F y sn) x at hsn_smooth
    have hdist : |sstar - sn| < ε := by
      rw [abs_lt]
      constructor <;> linarith [hsn_ball.1, hsn_ball.2]
    exact ⟨hstep sn hsn hsn_smooth sstar hsstar hdist, hsstar⟩
  have hsub : _root_.Set.Ioo a b ⊆ good :=
    isPreconnected_Ioo.subset_of_closure_inter_subset hgood_open
      ⟨t₀, ht₀, ht₀_good⟩ hgood_closed
  exact (show ContDiffAt ℝ ∞ (fun y ↦ F y target) x from
    (hsub htarget).1).contDiffWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.Flow.flow_slice_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.Flow.flow_slice_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.Flow.flow_slice_smooth ``Submission.DifferentialGeometry.Analysis.ODE.Flow.flow_slice_smooth

end UniformRestart

end Flow
end ODE
end Analysis
end DifferentialGeometry
