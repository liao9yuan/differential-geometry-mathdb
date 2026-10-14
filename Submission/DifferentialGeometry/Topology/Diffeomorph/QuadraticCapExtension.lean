import Submission.DifferentialGeometry.Topology.Diffeomorph.Fiberwise
import Submission.DifferentialGeometry.Topology.Diffeomorph.QuadraticFiberFlow
import Submission.DifferentialGeometry.Analysis.Calculus.SmoothMax

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set _root_.Metric _root_.Filter
open scoped _root_.ContDiff _root_.Manifold _root_.Topology
open _root_.Submission.DifferentialGeometry.Analysis.ODE

namespace Diffeomorph
open _root_.Diffeomorph

open _root_.Diffeomorph in
private theorem exists_contDiff_upper_clamp {b d : ℝ} (hbd : b < d) :
    ∃ σ : ℝ → ℝ, ContDiff ℝ ∞ σ ∧
      (∀ t ≤ b, σ t = t) ∧ (∀ t, σ t ≤ d) ∧ (∀ t, b ≤ t → b ≤ σ t) := by
  let ε := (d - b) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  let σ : ℝ → ℝ := fun t => -Real.smoothMax ε (-t) (-d)
  have hσ : ContDiff ℝ ∞ σ :=
    ((Real.smoothMax.contDiff ε).comp (contDiff_id.neg.prodMk contDiff_const)).neg
  have heq (t : ℝ) (ht : t ≤ b) : σ t = t := by
    dsimp [σ]
    rw [Real.smoothMax.eq_max_of_le hε (by
      rw [show -t - -d = d - t by ring, abs_of_nonneg (by linarith)]
      dsimp [ε]
      linarith), max_eq_left (by linarith), neg_neg]
  refine ⟨σ, hσ, heq, ?_, ?_⟩
  · intro t
    have h := (le_max_right (-t) (-d)).trans (Real.smoothMax.max_le hε (-t) (-d))
    dsimp [σ]
    linarith
  · intro t ht
    have h := Real.smoothMax.monotone_left ε (-d) (show -t ≤ -b by linarith)
    have hb := heq b le_rfl
    dsimp [σ] at *
    linarith

run_cmd do
  let target := ``Submission.Diffeomorph.exists_contDiff_upper_clamp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Diffeomorph.exists_contDiff_upper_clamp target :: scope.openDecls } }

open _root_.Diffeomorph in
theorem exists_diffeomorph_eqOn_quadratic_cap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : ℝ → E ≃ₘ[ℝ] E)
    (hG : ContDiff ℝ ∞ (fun z : ℝ × E => G z.1 z.2))
    (hGi : ContDiff ℝ ∞ (fun z : ℝ × E => (G z.1).symm z.2))
    (A : (E × ℝ) ≃ₘ[ℝ] (E × ℝ)) (hA : ∀ p, (A p).2 = p.2)
    {b c δ r R : ℝ} (hbc : b < c) (hδ : 0 < δ) (hr : 0 ≤ r) (hrR : r < R)
    (hmodel : ∀ t ∈ _root_.Set.Icc (b - δ) (b + δ), ∀ x ∈ _root_.Metric.closedBall (0 : E) R,
      G t x = (A (quadraticLevelScaling b c x t, t)).1) :
    ∃ D : (E × ℝ) ≃ₘ[ℝ] (E × ℝ), (∀ p, (D p).2 = p.2) ∧
      (∀ t ≤ b, ∀ x, D (quadraticLevelScaling b c x t, t) = (G t x, t)) ∧
      ∃ ρ > r, ∀ t, b ≤ t → ∀ x ∈ _root_.Metric.ball (0 : E) ρ, D (x, t) = A (x, t) := by
  let ρ := (r + R) / 2
  have hrρ : r < ρ := by dsimp [ρ]; linarith
  have hρR : ρ < R := by dsimp [ρ]; linarith
  have hρ : 0 < ρ := lt_of_le_of_lt hr hrρ
  let k : ℝ → ℝ := fun t => (Real.sqrt ((t - c) / (b - c)))⁻¹
  have hkb : k b = 1 := by simp [k, sub_ne_zero.mpr hbc.ne]
  have hk : ContinuousAt k b :=
    ((Real.continuous_sqrt.comp
      ((continuous_id.sub continuous_const).div_const _)).continuousAt).inv₀
      (by simp [sub_ne_zero.mpr hbc.ne])
  have hnear : ∀ᶠ t in 𝓝 b, k t * ρ < R :=
    (hk.mul_const ρ).eventually
      (isOpen_Iio.mem_nhds (by simpa only [_root_.Set.mem_Iio, hkb, one_mul] using hρR))
  obtain ⟨η, hη, hηbound⟩ := Metric.eventually_nhds_iff.mp hnear
  let d := b + _root_.Min.min η (_root_.Min.min δ (c - b)) / 2
  have hbd : b < d := by
    have hm : 0 < _root_.Min.min η (_root_.Min.min δ (c - b)) := lt_min hη (lt_min hδ (sub_pos.mpr hbc))
    dsimp [d]
    linarith
  have hdη : d - b < η := by dsimp [d]; have := min_le_left η (_root_.Min.min δ (c - b)); linarith
  have hdδ : d < b + δ := by
    have hh := (min_le_right η (_root_.Min.min δ (c - b))).trans (min_le_left δ (c - b))
    dsimp [d]
    linarith
  have hdc : d < c := by
    have hh := (min_le_right η (_root_.Min.min δ (c - b))).trans (min_le_right δ (c - b))
    dsimp [d]
    linarith
  obtain ⟨σ, hσ, hσlo, hσd, hσhi⟩ := exists_contDiff_upper_clamp hbd
  have hσc (t : ℝ) : σ t < c := (hσd t).trans_lt hdc
  have hratio (t : ℝ) : 0 < (σ t - c) / (b - c) :=
    div_pos_of_neg_of_neg (sub_neg.mpr (hσc t)) (sub_neg.mpr hbc)
  have hsqrt : ContDiff ℝ ∞ (fun t => Real.sqrt ((σ t - c) / (b - c))) :=
    ((hσ.sub contDiff_const).div_const _).sqrt (fun t => (hratio t).ne')
  have hkσ : ContDiff ℝ ∞ (fun t => k (σ t)) :=
    hsqrt.inv (fun t => (Real.sqrt_pos.mpr (hratio t)).ne')
  have hkσpos (t : ℝ) : 0 < k (σ t) := inv_pos.mpr (Real.sqrt_pos.mpr (hratio t))
  let S := Diffeomorph.fiberwiseSmul (E := E) hkσ (fun t => (hkσpos t).ne')
  let A' : (E × ℝ) ≃ₘ⟮(𝓘(ℝ, E)).prod 𝓘(ℝ, ℝ), (𝓘(ℝ, E)).prod 𝓘(ℝ, ℝ)⟯ (E × ℝ) :=
    { toEquiv := A.toEquiv
      contMDiff_toFun := by
        rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
        exact A.contMDiff
      contMDiff_invFun := by
        rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
        exact A.symm.contMDiff }
  let P : (E × ℝ) ≃ₘ[ℝ] (E × ℝ) :=
    { toEquiv := Equiv.prodCongrLeft (fun t => (G (σ t)).toEquiv)
      contMDiff_toFun := ((hG.comp ((hσ.comp contDiff_snd).prodMk contDiff_fst)).prodMk
        contDiff_snd).contMDiff
      contMDiff_invFun := ((hGi.comp ((hσ.comp contDiff_snd).prodMk contDiff_fst)).prodMk
        contDiff_snd).contMDiff }
  let Q : (E × ℝ) ≃ₘ[ℝ] (E × ℝ) :=
    { toEquiv := Equiv.prodCongrLeft (fun t => (A'.restrictFiber hA (σ t)).symm.toEquiv)
      contMDiff_toFun := ((A.symm.contDiff.comp
        (contDiff_fst.prodMk (hσ.comp contDiff_snd))).fst.prodMk contDiff_snd).contMDiff
      contMDiff_invFun := ((A.contDiff.comp
        (contDiff_fst.prodMk (hσ.comp contDiff_snd))).fst.prodMk contDiff_snd).contMDiff }
  let D := S.trans (P.trans (Q.trans A))
  have hD (x : E) (t : ℝ) :
      D (x, t) = A ((A.symm (G (σ t) (k (σ t) • x), σ t)).1, t) := rfl
  have hscale (t : ℝ) (x : E) :
      quadraticLevelScaling b c (k (σ t) • x) (σ t) = x := by
    rw [quadraticLevelScaling, smul_smul]
    change (Real.sqrt ((σ t - c) / (b - c)) *
      (Real.sqrt ((σ t - c) / (b - c)))⁻¹) • x = x
    rw [mul_inv_cancel₀ (Real.sqrt_pos.mpr (hratio t)).ne', one_smul]
  refine ⟨D, ?_, ?_, ρ, hrρ, ?_⟩
  · intro p
    rw [show p = (p.1, p.2) from rfl, hD, hA]
  · intro t ht x
    have hst := hσlo t ht
    have hpos : 0 < Real.sqrt ((t - c) / (b - c)) :=
      Real.sqrt_pos.mpr (div_pos_of_neg_of_neg (sub_neg.mpr (ht.trans_lt hbc)) (sub_neg.mpr hbc))
    have hcancel : k t • quadraticLevelScaling b c x t = x := by
      dsimp only [k, quadraticLevelScaling]
      rw [smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
    rw [hD, hst, hcancel]
    have hAt : (A.symm (G t x, t)).2 = t :=
      (hA (A.symm (G t x, t))).symm.trans (congrArg Prod.snd (A.apply_symm_apply _))
    have hp : ((A.symm (G t x, t)).1, t) = A.symm (G t x, t) :=
      Prod.ext rfl hAt.symm
    rw [hp, A.apply_symm_apply]
  · intro t ht x hx
    have hbt := hσhi t ht
    have hmem : σ t ∈ _root_.Set.Icc (b - δ) (b + δ) := ⟨by linarith, (hσd t).trans hdδ.le⟩
    have hbound : k (σ t) * ρ < R := hηbound (by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hbt)]
      linarith [hσd t])
    have hxR : k (σ t) • x ∈ _root_.Metric.closedBall (0 : E) R := by
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg (hkσpos t).le]
      have hxn : ‖x‖ < ρ := mem_ball_zero_iff.mp hx
      exact ((mul_lt_mul_of_pos_left hxn (hkσpos t)).trans hbound).le
    rw [hD, hmodel (σ t) hmem _ hxR, hscale]
    have hp : ((A (x, σ t)).1, σ t) = A (x, σ t) := Prod.ext rfl (hA (x, σ t)).symm
    rw [hp, A.symm_apply_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.exists_diffeomorph_eqOn_quadratic_cap then
    throwError "Refusing to shadow existing declaration Diffeomorph.exists_diffeomorph_eqOn_quadratic_cap"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.exists_diffeomorph_eqOn_quadratic_cap ``Submission.Diffeomorph.exists_diffeomorph_eqOn_quadratic_cap

end Diffeomorph
