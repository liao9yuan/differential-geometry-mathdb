import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Fiber.CoerciveBilinearInverse
import Submission.DifferentialGeometry.Analysis.ODE.Existence.GlobalLipschitzAffine
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.MeanValue

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Metric
open scoped _root_.NNReal _root_.Topology

namespace DifferentialGeometry.Analysis.ODE

theorem coerciveMassODE_exists
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V]
    {mass : ℝ → V →L[ℝ] V →L[ℝ] ℝ}
    {resid : ℝ → V → (V →L[ℝ] ℝ)} {T c A : ℝ} {L : ℝ≥0}
    (hT : 0 < T) (hc : 0 < c) (hA : 0 ≤ A)
    (hmass : ContinuousOn mass (_root_.Set.Icc (0 : ℝ) T))
    (hcoer : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T, ∀ v : V,
      c * ‖v‖ * ‖v‖ ≤ mass t v v)
    (hlip : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T, LipschitzWith L (resid t))
    (hcont : ∀ v : V, ContinuousOn (fun t => resid t v) (_root_.Set.Icc (0 : ℝ) T))
    (haff : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T, ∀ v : V,
      ‖resid t v‖ ≤ A + (L : ℝ) * ‖v‖)
    (v₀ : V) :
    let hco : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T, IsCoercive (mass t) := fun t ht =>
      ⟨c, hc, hcoer t ht⟩
    ∃ γ : ℝ → V, γ 0 = v₀ ∧ ContinuousOn γ (_root_.Set.Icc (0 : ℝ) T) ∧
      ∀ t, (ht : t ∈ _root_.Set.Ico (0 : ℝ) T) →
        HasDerivWithinAt γ
          ((hco t ⟨ht.1, le_of_lt ht.2⟩).sharpCLM (resid t (γ t)))
          (_root_.Set.Ici (0 : ℝ)) t := by
  classical
  dsimp only
  let hco : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T, IsCoercive (mass t) := fun t ht =>
    ⟨c, hc, hcoer t ht⟩
  let cinv : ℝ≥0 := ⟨c⁻¹, inv_nonneg.mpr hc.le⟩
  let K : ℝ≥0 := cinv * L
  let f : ℝ → V → V := fun t v =>
    if ht : t ∈ _root_.Set.Icc (0 : ℝ) T then
      (hco t ht).sharpCLM (resid t v)
    else 0
  have hsharp_norm : ∀ t (ht : t ∈ _root_.Set.Icc (0 : ℝ) T),
      ‖(hco t ht).sharpCLM‖ ≤ c⁻¹ := by
    intro t ht
    exact (hco t ht).sharpCLM_norm_le hc (hcoer t ht)
  have hlip_f : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T, LipschitzWith K (f t) := by
    intro t ht
    have hsharp : LipschitzWith ‖(hco t ht).sharpCLM‖₊
        (hco t ht).sharpCLM := (hco t ht).sharpCLM.lipschitz
    have hcomp := hsharp.comp (hlip t ht)
    have hnorm_nn : ‖(hco t ht).sharpCLM‖₊ ≤ cinv := by
      exact_mod_cast hsharp_norm t ht
    have hKL : ‖(hco t ht).sharpCLM‖₊ * L ≤ K := by
      simpa only [K, mul_comm] using mul_le_mul_left hnorm_nn L
    rw [show f t = (hco t ht).sharpCLM ∘ resid t by
      funext v
      simp only [f, dif_pos ht, Function.comp_apply]]
    exact hcomp.weaken hKL
  have hsharp_cont : Continuous
      (fun t : _root_.Set.Icc (0 : ℝ) T => (hco t t.2).sharpCLM) := by
    exact IsCoercive.sharpCLM_cont_sub mass hmass hco
  have hcont_f : ∀ v : V, ContinuousOn (fun t => f t v) (_root_.Set.Icc (0 : ℝ) T) := by
    intro v
    rw [continuousOn_iff_continuous_domRestrict]
    have hres : Continuous (fun t : _root_.Set.Icc (0 : ℝ) T => resid t v) :=
      (hcont v).domRestrict
    have happ := hsharp_cont.clm_apply hres
    convert happ using 1
    ext t
    simp only [f, Set.domRestrict_apply, dif_pos t.property]
  have haff_f : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T, ∀ v : V,
      ‖f t v‖ ≤ c⁻¹ * A + (K : ℝ) * ‖v‖ := by
    intro t ht v
    have hop := ContinuousLinearMap.le_opNorm
      (hco t ht).sharpCLM (resid t v)
    have hcnn : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
    calc
      ‖f t v‖ = ‖(hco t ht).sharpCLM (resid t v)‖ := by
        simp only [f, dif_pos ht]
      _ ≤ ‖(hco t ht).sharpCLM‖ * ‖resid t v‖ := hop
      _ ≤ c⁻¹ * (A + (L : ℝ) * ‖v‖) :=
        mul_le_mul (hsharp_norm t ht) (haff t ht v) (norm_nonneg _) hcnn
      _ = c⁻¹ * A + (K : ℝ) * ‖v‖ := by
        simp only [K, NNReal.coe_mul]
        rw [show (cinv : ℝ) = c⁻¹ from rfl, mul_add, mul_assoc]
  have hA' : 0 ≤ c⁻¹ * A := mul_nonneg (inv_nonneg.mpr hc.le) hA
  obtain ⟨γ, hγ0, hγcont, hγderiv⟩ :=
    forward_solution_of_lipschitzWith_affineBound
      (E := V) (f := f) hT hA' hlip_f hcont_f haff_f v₀
  refine ⟨γ, hγ0, hγcont, ?_⟩
  intro t ht
  have ht' : t ∈ _root_.Set.Icc (0 : ℝ) T := ⟨ht.1, le_of_lt ht.2⟩
  simpa only [f, dif_pos ht'] using hγderiv t ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.coerciveMassODE_exists then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.coerciveMassODE_exists"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.coerciveMassODE_exists ``Submission.DifferentialGeometry.Analysis.ODE.coerciveMassODE_exists

theorem coerOn_of_lip
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V → V →L[ℝ] V →L[ℝ] ℝ) {c R : ℝ} {K : ℝ≥0}
    (hR : 0 ≤ R)
    (hB_lip : LipschitzOnWith K B (_root_.Metric.closedBall (0 : V) R))
    (hB_zero : ∀ v : V, c * ‖v‖ * ‖v‖ ≤ B 0 v v)
    (hKR : (K : ℝ) * R ≤ c / 2) :
    ∀ u ∈ _root_.Metric.closedBall (0 : V) R, ∀ v : V,
      (c / 2) * ‖v‖ * ‖v‖ ≤ B u v v := by
  intro u hu v
  have hzero : (0 : V) ∈ _root_.Metric.closedBall (0 : V) R :=
    _root_.Metric.mem_closedBall_self hR
  have huR : ‖u‖ ≤ R := by
    simpa only [_root_.Metric.mem_closedBall, dist_zero_right] using hu
  have hdiff : ‖B u - B 0‖ ≤ (K : ℝ) * R := by
    calc
      ‖B u - B 0‖ ≤ (K : ℝ) * ‖u‖ := by
        simpa only [dist_eq_norm, sub_zero] using
          hB_lip.dist_le_mul u hu 0 hzero
      _ ≤ (K : ℝ) * R :=
        mul_le_mul_of_nonneg_left huR K.coe_nonneg
  let D : V →L[ℝ] V →L[ℝ] ℝ := B u - B 0
  have habs : |D v v| ≤ (c / 2) * ‖v‖ * ‖v‖ := by
    calc
      |D v v| = ‖D v v‖ := by rw [Real.norm_eq_abs]
      _ ≤ ‖D v‖ * ‖v‖ := (D v).le_opNorm v
      _ ≤ (‖D‖ * ‖v‖) * ‖v‖ := by
        exact mul_le_mul_of_nonneg_right (D.le_opNorm v) (norm_nonneg v)
      _ ≤ (((K : ℝ) * R) * ‖v‖) * ‖v‖ := by
        gcongr
      _ ≤ ((c / 2) * ‖v‖) * ‖v‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hKR (norm_nonneg v)) (norm_nonneg v)
      _ = (c / 2) * ‖v‖ * ‖v‖ := rfl
  have hDlow : -((c / 2) * ‖v‖ * ‖v‖) ≤ D v v :=
    neg_le_of_abs_le habs
  have heval : B u v v = B 0 v v + D v v := by
    simp only [D, sub_apply]
    ring
  rw [heval]
  calc
    (c / 2) * ‖v‖ * ‖v‖ =
        c * ‖v‖ * ‖v‖ - (c / 2) * ‖v‖ * ‖v‖ := by ring
    _ ≤ B 0 v v + D v v := add_le_add (hB_zero v) hDlow

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.coerOn_of_lip then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.coerOn_of_lip"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.coerOn_of_lip ``Submission.DifferentialGeometry.Analysis.ODE.coerOn_of_lip

theorem exists_state_mass_solution
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V]
    {mass : ℝ → V → V →L[ℝ] V →L[ℝ] ℝ}
    {resid : ℝ → V → (V →L[ℝ] ℝ)}
    {T R c A : ℝ} {Km Kr : ℝ≥0}
    (hT : 0 < T) (hR : 0 < R) (hc : 0 < c) (hA : 0 ≤ A)
    (hcoer : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T,
      ∀ u ∈ _root_.Metric.closedBall (0 : V) R, ∀ v : V,
        c * ‖v‖ * ‖v‖ ≤ mass t u v v)
    (hmass_lip : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T,
      LipschitzOnWith Km (mass t) (_root_.Metric.closedBall (0 : V) R))
    (hmass_time : ∀ u ∈ _root_.Metric.closedBall (0 : V) R,
      ContinuousOn (fun t ↦ mass t u) (_root_.Set.Icc (0 : ℝ) T))
    (hres_lip : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T,
      LipschitzOnWith Kr (resid t) (_root_.Metric.closedBall (0 : V) R))
    (hres_time : ∀ u ∈ _root_.Metric.closedBall (0 : V) R,
      ContinuousOn (fun t ↦ resid t u) (_root_.Set.Icc (0 : ℝ) T))
    (hres_bound : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T,
      ∀ u ∈ _root_.Metric.closedBall (0 : V) R, ‖resid t u‖ ≤ A) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ T ∧
      ∃ γ : ℝ → V, γ 0 = 0 ∧ ContinuousOn γ (_root_.Set.Icc (0 : ℝ) τ) ∧
        (∀ t ∈ _root_.Set.Icc (0 : ℝ) τ, γ t ∈ _root_.Metric.closedBall (0 : V) R) ∧
        ∃ velocity : ℝ → V,
          (∀ t, t ∈ _root_.Set.Icc (0 : ℝ) τ →
            HasDerivWithinAt γ (velocity t) (_root_.Set.Icc (0 : ℝ) τ) t) ∧
          ∀ t, t ∈ _root_.Set.Icc (0 : ℝ) τ →
            mass t (γ t) (velocity t) = resid t (γ t) := by
  classical
  let cinv : ℝ≥0 := ⟨c⁻¹, inv_nonneg.mpr hc.le⟩
  let An : ℝ≥0 := ⟨A, hA⟩
  let Lf : ℝ≥0 := cinv * An
  let Kf : ℝ≥0 := cinv * Kr + cinv * (Km * (cinv * An))
  have hKfcoe : (Kf : ℝ) =
      c⁻¹ * (Kr : ℝ) + c⁻¹ * ((Km : ℝ) * (c⁻¹ * A)) := by
    with_unfolding_all rfl
  let τ : ℝ := _root_.Min.min T (R / ((Lf : ℝ) + 1))
  have hden : 0 < (Lf : ℝ) + 1 := by positivity
  have hτ : 0 < τ := lt_min hT (div_pos hR hden)
  have hτT : τ ≤ T := min_le_left _ _
  have hτR : τ ≤ R / ((Lf : ℝ) + 1) := min_le_right _ _
  have hLfR : (Lf : ℝ) * τ ≤ R := by
    calc
      (Lf : ℝ) * τ ≤ (Lf : ℝ) * (R / ((Lf : ℝ) + 1)) := by
        exact mul_le_mul_of_nonneg_left hτR Lf.coe_nonneg
      _ = ((Lf : ℝ) / ((Lf : ℝ) + 1)) * R := by ring
      _ ≤ 1 * R := by
        apply mul_le_mul_of_nonneg_right _ hR.le
        exact (div_le_one hden).2 (by linarith)
      _ = R := one_mul R
  let hco : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T,
      ∀ u ∈ _root_.Metric.closedBall (0 : V) R, IsCoercive (mass t u) :=
    fun t ht u hu ↦ ⟨c, hc, hcoer t ht u hu⟩
  let f : ℝ → V → V := fun t u ↦
    if ht : t ∈ _root_.Set.Icc (0 : ℝ) T then
      if hu : u ∈ _root_.Metric.closedBall (0 : V) R then
        (hco t ht u hu).sharpCLM (resid t u)
      else 0
    else 0
  have htime_sub : _root_.Set.Icc (0 : ℝ) τ ⊆ _root_.Set.Icc (0 : ℝ) T := by
    intro t ht
    exact ⟨ht.1, ht.2.trans hτT⟩
  have hfnorm : ∀ t u, ‖f t u‖ ≤ (Lf : ℝ) := by
    intro t u
    by_cases ht : t ∈ _root_.Set.Icc (0 : ℝ) T
    · by_cases hu : u ∈ _root_.Metric.closedBall (0 : V) R
      · have hsharp : ‖(hco t ht u hu).sharpCLM‖ ≤ c⁻¹ :=
          (hco t ht u hu).sharpCLM_norm_le hc (hcoer t ht u hu)
        calc
          ‖f t u‖ = ‖(hco t ht u hu).sharpCLM (resid t u)‖ := by
            simp only [f, dif_pos ht, dif_pos hu]
          _ ≤ ‖(hco t ht u hu).sharpCLM‖ * ‖resid t u‖ :=
            ContinuousLinearMap.le_opNorm _ _
          _ ≤ c⁻¹ * A := by
            exact mul_le_mul hsharp (hres_bound t ht u hu)
              (norm_nonneg _) (inv_nonneg.mpr hc.le)
          _ = (Lf : ℝ) := by rfl
      · simp only [f, dif_pos ht, dif_neg hu, norm_zero]
        exact Lf.coe_nonneg
    · simp only [f, dif_neg ht, norm_zero]
      exact Lf.coe_nonneg
  have hflip : ∀ t ∈ _root_.Set.Icc (0 : ℝ) τ,
      LipschitzOnWith Kf (f t) (_root_.Metric.closedBall (0 : V) R) := by
    intro t ht
    have htT : t ∈ _root_.Set.Icc (0 : ℝ) T := htime_sub ht
    refine LipschitzOnWith.of_dist_le_mul ?_
    intro u hu v hv
    have hm : ‖mass t v - mass t u‖ ≤ (Km : ℝ) * ‖u - v‖ := by
      have h := (hmass_lip t htT).dist_le_mul v hv u hu
      rw [dist_eq_norm, dist_eq_norm] at h
      calc
        ‖mass t v - mass t u‖ ≤ (Km : ℝ) * ‖v - u‖ := h
        _ = (Km : ℝ) * ‖u - v‖ := by rw [norm_sub_rev]
    have hr : ‖resid t u - resid t v‖ ≤ (Kr : ℝ) * ‖u - v‖ := by
      simpa only [dist_eq_norm] using
        (hres_lip t htT).dist_le_mul u hu v hv
    have hs := (hco t htT u hu).sharp_var_le (hco t htT v hv)
      hc hc (hcoer t htT u hu) (hcoer t htT v hv)
      (resid t u) (resid t v)
    rw [dist_eq_norm]
    simp only [f, dif_pos htT, dif_pos hu, dif_pos hv]
    calc
      ‖(hco t htT u hu).sharpCLM (resid t u) -
          (hco t htT v hv).sharpCLM (resid t v)‖
          ≤ c⁻¹ * ‖resid t u - resid t v‖ +
            c⁻¹ * (‖mass t v - mass t u‖ *
              (c⁻¹ * ‖resid t v‖)) := by
            simpa only [IsCoercive.sharpCLM_apply] using hs
      _ ≤ c⁻¹ * ((Kr : ℝ) * ‖u - v‖) +
            c⁻¹ * (((Km : ℝ) * ‖u - v‖) * (c⁻¹ * A)) := by
            gcongr
            exact hres_bound t htT v hv
      _ = (Kf : ℝ) * _root_.Dist.dist u v := by
            rw [dist_eq_norm]
            rw [hKfcoe]
            ring
  have hftime : ∀ u ∈ _root_.Metric.closedBall (0 : V) R,
      ContinuousOn (fun t ↦ f t u) (_root_.Set.Icc (0 : ℝ) τ) := by
    intro u hu
    have hm : ContinuousOn (fun t ↦ mass t u) (_root_.Set.Icc (0 : ℝ) τ) :=
      (hmass_time u hu).mono htime_sub
    let hcsub : ∀ t ∈ _root_.Set.Icc (0 : ℝ) τ, IsCoercive (mass t u) :=
      fun t ht ↦ hco t (htime_sub ht) u hu
    have hsharp : Continuous
        (fun t : _root_.Set.Icc (0 : ℝ) τ ↦ (hcsub t t.2).sharpCLM) :=
      IsCoercive.sharpCLM_cont_sub (fun t ↦ mass t u) hm hcsub
    have hr : Continuous (fun t : _root_.Set.Icc (0 : ℝ) τ ↦ resid t u) :=
      ((hres_time u hu).mono htime_sub).domRestrict
    rw [continuousOn_iff_continuous_domRestrict]
    have happ := hsharp.clm_apply hr
    convert happ using 1
    funext t
    simp only [f, Set.domRestrict_apply, dif_pos (htime_sub t.2), dif_pos hu]
  let tzero : _root_.Set.Icc (0 : ℝ) τ := ⟨0, by exact ⟨le_rfl, hτ.le⟩⟩
  let aN : ℝ≥0 := ⟨R, hR.le⟩
  have hPL : IsPicardLindelof f tzero (0 : V) aN 0 Lf Kf :=
    { lipschitzOnWith := hflip
      continuousOn := hftime
      norm_le := fun t _ u _ ↦ hfnorm t u
      mul_max_le := by
        change (Lf : ℝ) * _root_.Max.max (τ - 0) (0 - 0) ≤ R - 0
        simpa only [sub_zero, max_eq_left hτ.le] using hLfR }
  obtain ⟨γ, hγ0, hγderiv⟩ :=
    hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  have hγcont : ContinuousOn γ (_root_.Set.Icc (0 : ℝ) τ) :=
    fun t ht ↦ (hγderiv t ht).continuousWithinAt
  have hγball : ∀ t ∈ _root_.Set.Icc (0 : ℝ) τ,
      γ t ∈ _root_.Metric.closedBall (0 : V) R := by
    have hmove := norm_image_sub_le_of_norm_deriv_le_segment'
      hγderiv (fun t ht ↦ hfnorm t (γ t))
    intro t ht
    rw [_root_.Metric.mem_closedBall, dist_zero_right]
    calc
      ‖γ t‖ = ‖γ t - γ 0‖ := by rw [hγ0, sub_zero]
      _ ≤ (Lf : ℝ) * (t - 0) := hmove t ht
      _ ≤ (Lf : ℝ) * τ := by
        apply mul_le_mul_of_nonneg_left _ Lf.coe_nonneg
        simpa only [sub_zero] using ht.2
      _ ≤ R := hLfR
  let velocity : ℝ → V := fun t ↦ f t (γ t)
  refine ⟨τ, hτ, hτT, γ, hγ0, hγcont, hγball, velocity, ?_, ?_⟩
  · intro t ht
    exact hγderiv t ht
  · intro t ht
    have htT : t ∈ _root_.Set.Icc (0 : ℝ) T := htime_sub ht
    have hu : γ t ∈ _root_.Metric.closedBall (0 : V) R := hγball t ht
    change mass t (γ t) (f t (γ t)) = resid t (γ t)
    rw [show f t (γ t) =
        (hco t htT (γ t) hu).sharpCLM (resid t (γ t)) by
      simp only [f, dif_pos htT, dif_pos hu]]
    simpa only [IsCoercive.sharpCLM_apply] using
      (hco t htT (γ t) hu).apply_sharp (resid t (γ t))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.exists_state_mass_solution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.exists_state_mass_solution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.exists_state_mass_solution ``Submission.DifferentialGeometry.Analysis.ODE.exists_state_mass_solution

end DifferentialGeometry.Analysis.ODE

end
