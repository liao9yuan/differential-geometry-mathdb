import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Extend

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem integralCurve_eqOn_Icc_of_locallyLipschitzOn
    {f : ℝ → E → E} {γ η : ℝ → E} {a b t₀ : ℝ}
    (hf : LocallyLipschitzOn (_root_.Set.Icc a b ×ˢ (_root_.Set.univ : Set E)) (Function.uncurry f))
    (hγ : IsIntegralCurveOn γ f (_root_.Set.Icc a b)) (hη : IsIntegralCurveOn η f (_root_.Set.Icc a b))
    (ht₀ : t₀ ∈ _root_.Set.Icc a b) (hinit : γ t₀ = η t₀) : _root_.Set.EqOn γ η (_root_.Set.Icc a b) := by
  let S : Set (ℝ × E) := (fun t => (t, γ t)) '' _root_.Set.Icc a b ∪
    (fun t => (t, η t)) '' _root_.Set.Icc a b
  have hS : IsCompact S :=
    (isCompact_Icc.image_of_continuousOn (continuousOn_id.prodMk hγ.continuousOn)).union
      (isCompact_Icc.image_of_continuousOn (continuousOn_id.prodMk hη.continuousOn))
  have hsub : S ⊆ _root_.Set.Icc a b ×ˢ (_root_.Set.univ : Set E) := by
    rintro p (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩) <;> exact ⟨ht, _root_.Set.mem_univ _⟩
  obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hS (hf.mono hsub)
  let s : ℝ → Set E := fun t => {v | (t, v) ∈ S}
  have hLip (t : ℝ) : LipschitzOnWith K (f t) (s t) := by
    intro v hv w hw
    simpa only [Function.uncurry_apply_pair, Prod.edist_eq, _root_.PseudoEMetricSpace.edist_self, zero_max] using hK hv hw
  have hγmem (t : ℝ) (ht : t ∈ _root_.Set.Icc a b) : γ t ∈ s t :=
    Or.inl ⟨t, ht, rfl⟩
  have hηmem (t : ℝ) (ht : t ∈ _root_.Set.Icc a b) : η t ∈ s t :=
    Or.inr ⟨t, ht, rfl⟩
  rw [← _root_.Set.Icc_union_Icc_eq_Icc ht₀.1 ht₀.2]
  refine EqOn.union ?_ ?_
  · have hI : _root_.Set.Icc a t₀ ⊆ _root_.Set.Icc a b := _root_.Set.Icc_subset_Icc_right ht₀.2
    exact ODE_solution_unique_of_mem_Icc_left
      (fun t _ => hLip t) (hγ.continuousOn.mono hI)
      (fun t ht => (hγ t (hI (_root_.Set.Ioc_subset_Icc_self ht))).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsLE_of_mem ⟨ht.1, ht.2.trans ht₀.2⟩))
      (fun t ht => hγmem t (hI (_root_.Set.Ioc_subset_Icc_self ht))) (hη.continuousOn.mono hI)
      (fun t ht => (hη t (hI (_root_.Set.Ioc_subset_Icc_self ht))).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsLE_of_mem ⟨ht.1, ht.2.trans ht₀.2⟩))
      (fun t ht => hηmem t (hI (_root_.Set.Ioc_subset_Icc_self ht))) hinit
  · have hI : _root_.Set.Icc t₀ b ⊆ _root_.Set.Icc a b := _root_.Set.Icc_subset_Icc_left ht₀.1
    exact ODE_solution_unique_of_mem_Icc_right
      (fun t _ => hLip t) (hγ.continuousOn.mono hI)
      (fun t ht => (hγ t (hI (_root_.Set.Ico_subset_Icc_self ht))).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨ht₀.1.trans ht.1, ht.2⟩))
      (fun t ht => hγmem t (hI (_root_.Set.Ico_subset_Icc_self ht))) (hη.continuousOn.mono hI)
      (fun t ht => (hη t (hI (_root_.Set.Ico_subset_Icc_self ht))).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨ht₀.1.trans ht.1, ht.2⟩))
      (fun t ht => hηmem t (hI (_root_.Set.Ico_subset_Icc_self ht))) hinit

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.ODE.integralCurve_eqOn_Icc_of_locallyLipschitzOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.ODE.integralCurve_eqOn_Icc_of_locallyLipschitzOn target :: scope.openDecls } }

theorem IsIntegralCurveOn.eqOn_of_locallyLipschitzOn
    {f : ℝ → E → E} {γ η : ℝ → E} {J : Set ℝ} {t₀ : ℝ}
    (hγ : IsIntegralCurveOn γ f J) (hη : IsIntegralCurveOn η f J)
    (hJ : J.OrdConnected) (hf : LocallyLipschitzOn (J ×ˢ (_root_.Set.univ : Set E)) (Function.uncurry f))
    (ht₀ : t₀ ∈ J) (hinit : γ t₀ = η t₀) : _root_.Set.EqOn γ η J := by
  intro t ht
  have hsub : _root_.Set.uIcc t₀ t ⊆ J := hJ.uIcc_subset ht₀ ht
  exact integralCurve_eqOn_Icc_of_locallyLipschitzOn
    (hf.mono (_root_.Set.prod_mono_left hsub)) (hγ.mono hsub) (hη.mono hsub)
    _root_.Set.left_mem_uIcc hinit _root_.Set.right_mem_uIcc

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Analysis.ODE.IsIntegralCurveOn
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.IsIntegralCurveOn.eqOn_of_locallyLipschitzOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.IsIntegralCurveOn.eqOn_of_locallyLipschitzOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.IsIntegralCurveOn.eqOn_of_locallyLipschitzOn ``Submission.DifferentialGeometry.Analysis.ODE.IsIntegralCurveOn.eqOn_of_locallyLipschitzOn

theorem IsIntegralCurveOn.eqOn_of_contDiffOn
    {f : ℝ → E → E} {γ η : ℝ → E} {J : Set ℝ} {t₀ : ℝ}
    (hγ : IsIntegralCurveOn γ f J) (hη : IsIntegralCurveOn η f J)
    (hJ : J.OrdConnected) (hf : ContDiffOn ℝ 1 (Function.uncurry f) (J ×ˢ (_root_.Set.univ : Set E)))
    (ht₀ : t₀ ∈ J) (hinit : γ t₀ = η t₀) : _root_.Set.EqOn γ η J :=
  IsIntegralCurveOn.eqOn_of_locallyLipschitzOn hγ hη hJ
    (hf.locallyLipschitzOn ((convex_iff_ordConnected.mpr hJ).prod convex_univ)) ht₀ hinit

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.IsIntegralCurveOn.eqOn_of_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.IsIntegralCurveOn.eqOn_of_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.IsIntegralCurveOn.eqOn_of_contDiffOn ``Submission.DifferentialGeometry.Analysis.ODE.IsIntegralCurveOn.eqOn_of_contDiffOn

end DifferentialGeometry.Analysis.ODE

section

open _root_.Filter
open scoped _root_.Topology

namespace DifferentialGeometry.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_eqOn_Icc_of_hasDerivAt_of_contDiffAt
    {v : ℝ → E → E} {f g : ℝ → E} {a b : ℝ} (hab : a < b)
    (hv : ContDiffAt ℝ 1 (Function.uncurry v) (b, f b))
    (hf : ∀ t ∈ _root_.Set.Ioo a b, HasDerivAt f (v t (f t)) t)
    (hg : ∀ t ∈ _root_.Set.Ioo a b, HasDerivAt g (v t (g t)) t)
    (hfb : ContinuousWithinAt f (_root_.Set.Iic b) b)
    (hgb : ContinuousWithinAt g (_root_.Set.Iic b) b)
    (hfg : f b = g b) :
    ∃ c ∈ _root_.Set.Ioo a b, _root_.Set.EqOn f g (_root_.Set.Icc c b) := by
  have hf_rhs : ContinuousWithinAt (fun t => v t (f t)) (_root_.Set.Iic b) b :=
    hv.continuousAt.tendsto.comp (continuousWithinAt_id.prodMk hfb).tendsto
  have hg_rhs : ContinuousWithinAt (fun t => v t (g t)) (_root_.Set.Iic b) b := by
    have hv' : ContinuousAt (Function.uncurry v) (b, g b) := by
      simpa only [hfg] using hv.continuousAt
    exact hv'.tendsto.comp (continuousWithinAt_id.prodMk hgb).tendsto
  have hfd : HasDerivWithinAt f (v b (f b)) (_root_.Set.Iic b) b := by
    refine hasDerivWithinAt_Iic_of_tendsto_deriv (s := _root_.Set.Ioo a b)
      (fun t ht => (hf t ht).differentiableAt.differentiableWithinAt)
      (hfb.mono (Ioo_subset_Iio_self.trans _root_.Set.Iio_subset_Iic_self)) (Ioo_mem_nhdsLT hab) ?_
    exact (hf_rhs.mono _root_.Set.Iio_subset_Iic_self).tendsto.congr'
      (Filter.eventuallyEq_of_mem (Ioo_mem_nhdsLT hab)
        fun t ht => (hf t ht).deriv).symm
  have hgd : HasDerivWithinAt g (v b (g b)) (_root_.Set.Iic b) b := by
    refine hasDerivWithinAt_Iic_of_tendsto_deriv (s := _root_.Set.Ioo a b)
      (fun t ht => (hg t ht).differentiableAt.differentiableWithinAt)
      (hgb.mono (Ioo_subset_Iio_self.trans _root_.Set.Iio_subset_Iic_self)) (Ioo_mem_nhdsLT hab) ?_
    exact (hg_rhs.mono _root_.Set.Iio_subset_Iic_self).tendsto.congr'
      (Filter.eventuallyEq_of_mem (Ioo_mem_nhdsLT hab)
        fun t ht => (hg t ht).deriv).symm
  obtain ⟨K, U, hU, hLip⟩ := hv.exists_lipschitzOnWith
  have hfgU : ∀ᶠ t in 𝓝[≤] b, (t, f t) ∈ U ∧ (t, g t) ∈ U := by
    apply Filter.Eventually.and
    · exact (continuousWithinAt_id.prodMk hfb).tendsto hU
    · apply (continuousWithinAt_id.prodMk hgb).tendsto
      simpa only [hfg, id_eq] using hU
  obtain ⟨c₀, hc₀, hc₀U⟩ := mem_nhdsLE_iff_exists_Icc_subset.mp hfgU
  let c := (_root_.Max.max a c₀ + b) / 2
  have hm : _root_.Max.max a c₀ < b := max_lt hab hc₀
  have hac : a < c := by dsimp [c]; linarith [le_max_left a c₀]
  have hc₀c : c₀ ≤ c := by dsimp [c]; linarith [le_max_right a c₀]
  have hcb : c < b := by dsimp [c]; linarith
  have hUsub : ∀ t ∈ _root_.Set.Icc c b, (t, f t) ∈ U ∧ (t, g t) ∈ U :=
    fun t ht => hc₀U ⟨hc₀c.trans ht.1, ht.2⟩
  let s : ℝ → Set E := fun t => {z | (t, z) ∈ U}
  have hLip' (t : ℝ) : LipschitzOnWith K (v t) (s t) := by
    intro z hz w hw
    simpa only [Function.uncurry_apply_pair, Prod.edist_eq, _root_.PseudoEMetricSpace.edist_self, zero_max]
      using hLip hz hw
  have hfc : ContinuousOn f (_root_.Set.Icc c b) := by
    intro t ht
    rcases lt_or_eq_of_le ht.2 with htb | rfl
    · exact (hf t ⟨hac.trans_le ht.1, htb⟩).continuousAt.continuousWithinAt
    · exact hfb.mono _root_.Set.Icc_subset_Iic_self
  have hgc : ContinuousOn g (_root_.Set.Icc c b) := by
    intro t ht
    rcases lt_or_eq_of_le ht.2 with htb | rfl
    · exact (hg t ⟨hac.trans_le ht.1, htb⟩).continuousAt.continuousWithinAt
    · exact hgb.mono _root_.Set.Icc_subset_Iic_self
  have hfd' : ∀ t ∈ _root_.Set.Ioc c b, HasDerivWithinAt f (v t (f t)) (_root_.Set.Iic t) t := by
    intro t ht
    rcases lt_or_eq_of_le ht.2 with htb | rfl
    · exact (hf t ⟨hac.trans ht.1, htb⟩).hasDerivWithinAt
    · exact hfd
  have hgd' : ∀ t ∈ _root_.Set.Ioc c b, HasDerivWithinAt g (v t (g t)) (_root_.Set.Iic t) t := by
    intro t ht
    rcases lt_or_eq_of_le ht.2 with htb | rfl
    · exact (hg t ⟨hac.trans ht.1, htb⟩).hasDerivWithinAt
    · exact hgd
  refine ⟨c, ⟨hac, hcb⟩, ?_⟩
  exact ODE_solution_unique_of_mem_Icc_left (fun t _ => hLip' t) hfc hfd'
    (fun t ht => (hUsub t (_root_.Set.Ioc_subset_Icc_self ht)).1) hgc hgd'
    (fun t ht => (hUsub t (_root_.Set.Ioc_subset_Icc_self ht)).2) hfg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.exists_eqOn_Icc_of_hasDerivAt_of_contDiffAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.exists_eqOn_Icc_of_hasDerivAt_of_contDiffAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.exists_eqOn_Icc_of_hasDerivAt_of_contDiffAt ``Submission.DifferentialGeometry.Analysis.ODE.exists_eqOn_Icc_of_hasDerivAt_of_contDiffAt

end DifferentialGeometry.Analysis.ODE

end
