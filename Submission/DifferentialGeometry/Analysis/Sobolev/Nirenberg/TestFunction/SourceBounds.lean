import Submission.DifferentialGeometry.Analysis.Sobolev.Nirenberg.TestFunction.WeakDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Set _root_.Metric _root_.Filter
open scoped _root_.ENNReal _root_.ContDiff

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction

open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBoundsNonSmooth

private theorem compact_diffQuot_integral_sq_le
    {d : ℕ} {u g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : _root_.MeasureTheory.MemLp u 2 _root_.MeasureTheory.MeasureSpace.volume) (hg : _root_.MeasureTheory.MemLp g 2 _root_.MeasureTheory.MeasureSpace.volume)
    (k : Fin d) (hweak : DeGiorgi.HasWeakPartialDeriv k g u _root_.Set.univ)
    (hucompact : HasCompactSupport u) (h : ℝ) :
    (∫ x, (diffQuot k h u x)^2) ≤ ∫ x, (g x)^2 := by
  by_cases hh : h = 0
  · simp only [hh, diffQuot_zero_h, Pi.zero_apply, zero_pow (by norm_num : 2 ≠ 0),
      _root_.MeasureTheory.integral_zero]
    exact _root_.MeasureTheory.integral_nonneg (fun x => sq_nonneg (g x))
  let K := _root_.Metric.cthickening |h| (tsupport u)
  have hKc : IsCompact K := hucompact.isCompact.cthickening
  have hsupport : Function.support (diffQuot k h u) ⊆ K := by
    intro x hx
    by_contra hxK
    have hx0 : u x = 0 := image_eq_zero_of_notMem_tsupport
      (fun hxu => hxK (_root_.Metric.self_subset_cthickening (tsupport u) hxu))
    have hshift : u (x + h • EuclideanSpace.single k 1) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hxu
      apply hxK
      apply _root_.Metric.closedBall_subset_cthickening hxu |h|
      rw [_root_.Metric.mem_closedBall, dist_eq_norm]
      have heq : x - (x + h • EuclideanSpace.single k 1) =
          (-h) • EuclideanSpace.single k 1 := by module
      rw [heq, norm_smul]
      simp only [PiLp.norm_single, _root_.NormOneClass.norm_one, mul_one, Real.norm_eq_abs, abs_neg, le_refl]
    change diffQuot k h u x ≠ 0 at hx
    exact hx (by simp [diffQuot, hx0, hshift])
  have hbound := integral_sq_diffQuot_le_integral_sq_weakPartial_meas hu hg k hweak
    MeasurableSet.univ hKc.measurableSet
    (by simpa only [hKc.isClosed.closure_eq] using hKc)
    (show 0 < |h| + 1 by positivity)
    (_root_.Set.subset_univ (_root_.Metric.cthickening (|h| + 1) (closure K))) hh
    (show |h| ≤ |h| + 1 by linarith)
  rw [Measure.restrict_univ] at hbound
  have heq : (∫ x in K, (diffQuot k h u x)^2) = ∫ x, (diffQuot k h u x)^2 := by
    apply _root_.MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hz : diffQuot k h u x = 0 := by
      by_contra hn
      exact hx (hsupport hn)
    rw [hz, zero_pow (by norm_num)]
  rwa [heq] at hbound

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.compact_diffQuot_integral_sq_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.compact_diffQuot_integral_sq_le target :: scope.openDecls } }

private theorem integral_sq_nirenbergTestFunction_le
    {d : ℕ} {u g η : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : _root_.MeasureTheory.MemLp u 2 _root_.MeasureTheory.MeasureSpace.volume) (hg : _root_.MeasureTheory.MemLp g 2 _root_.MeasureTheory.MeasureSpace.volume)
    (k : Fin d) (hweak : DeGiorgi.HasWeakPartialDeriv k g u _root_.Set.univ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηb : ∀ x, |η x| ≤ 1) {N : ℝ}
    (hηd : ∀ x, |fderiv ℝ η x (EuclideanSpace.single k 1)| ≤ N)
    (h : ℝ) :
    (∫ x, (nirenbergTestFunction k h η u x)^2) ≤
      2 * (∫ x, (η x * diffQuot k h g x)^2) +
        8 * N^2 * ∫ x in tsupport η, (diffQuot k h u x)^2 := by
  let F := fun x => (η x)^2 * diffQuot k h u x
  let G := fun x => (η x)^2 * diffQuot k h g x +
    2 * η x * fderiv ℝ η x (EuclideanSpace.single k 1) * diffQuot k h u x
  have hdqu := memLp_diffQuot_two k h hu
  have hdqg := memLp_diffQuot_two k h hg
  have hηsq := hη.pow 2
  have hηsqc : HasCompactSupport (fun x => (η x)^2) :=
    hηc.comp_left (g := fun y : ℝ => y^2) (by simp)
  have hηsqLp : _root_.MeasureTheory.MemLp (fun x => (η x)^2) ∞ volume := hηsq.continuous.memLp_of_hasCompactSupport hηsqc
  have hFLp : _root_.MeasureTheory.MemLp F 2 volume := hdqu.mul' hηsqLp
  have hDη := (hη.continuous_fderiv (by simp)).clm_apply
    (continuous_const : Continuous (fun _ : EuclideanSpace ℝ (Fin d) => EuclideanSpace.single k (1 : ℝ)))
  have hcoef : _root_.MeasureTheory.MemLp (fun x => 2 * η x * fderiv ℝ η x (EuclideanSpace.single k 1)) ∞ volume :=
    ((continuous_const.mul hη.continuous).mul hDη).memLp_of_hasCompactSupport
      ((hηc.mul_left).mul_right)
  have hGLp : _root_.MeasureTheory.MemLp G 2 volume :=
    (hdqg.mul' hηsqLp).add (hdqu.mul' hcoef)
  have hFweak : DeGiorgi.HasWeakPartialDeriv k G F univ := by
    have h0 := hasWeakPartialDeriv_cutoff_sq_mul_diffQuot k k h hη
      (by simpa only [Measure.restrict_univ] using hu.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
      (by simpa only [Measure.restrict_univ] using hg.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)) hweak
    have hd (x : EuclideanSpace ℝ (Fin d)) :
        fderiv ℝ (fun z => (η z)^2) x (EuclideanSpace.single k 1) =
          2 * η x * fderiv ℝ η x (EuclideanSpace.single k 1) := by
      rw [fderiv_fun_pow 2 (hη.differentiable (by simp) x)]
      simp only [smul_apply, smul_eq_mul]
      norm_num
    simpa only [hd] using h0
  have hbound := compact_diffQuot_integral_sq_le hFLp hGLp k hFweak
    hηsqc.mul_right (-h)
  change (∫ x, (nirenbergTestFunction k h η u x)^2) ≤ ∫ x, (G x)^2 at hbound
  have hηLp : _root_.MeasureTheory.MemLp η ∞ volume := hη.continuous.memLp_of_hasCompactSupport hηc
  have hmainLp : _root_.MeasureTheory.MemLp (fun x => η x * diffQuot k h g x) 2 volume := hdqg.mul' hηLp
  have hduLp : _root_.MeasureTheory.MemLp ((tsupport η).indicator (diffQuot k h u)) 2 volume := hdqu.indicator (isClosed_tsupport η).measurableSet
  have hp (x : EuclideanSpace ℝ (Fin d)) :
      (G x)^2 ≤ 2 * (η x * diffQuot k h g x)^2 +
        8 * N^2 * ((tsupport η).indicator (diffQuot k h u) x)^2 := by
    by_cases hx : x ∈ tsupport η
    · rw [_root_.Set.indicator_of_mem hx]
      have he : (η x)^2 ≤ 1 := (sq_le_one_iff_abs_le_one (η x)).mpr (hηb x)
      have hd : (fderiv ℝ η x (EuclideanSpace.single k 1))^2 ≤ N^2 :=
        by nlinarith [abs_le.mp (hηd x)]
      have h1 := mul_le_mul_of_nonneg_right he (sq_nonneg (η x * diffQuot k h g x))
      have h2 := mul_le_mul_of_nonneg_right he (sq_nonneg (fderiv ℝ η x (EuclideanSpace.single k 1) * diffQuot k h u x))
      have h3 := mul_le_mul_of_nonneg_right hd (sq_nonneg (diffQuot k h u x))
      dsimp only [G]
      nlinarith [sq_nonneg ((η x)^2 * diffQuot k h g x -
        2 * η x * fderiv ℝ η x (EuclideanSpace.single k 1) * diffQuot k h u x)]
    · have he : η x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [G, he, hx]
  have hfinal := _root_.MeasureTheory.integral_mono_ae hGLp.integrable_sq
    ((hmainLp.integrable_sq.const_mul 2).add (hduLp.integrable_sq.const_mul (8 * N^2)))
    (Eventually.of_forall hp)
  simp only [Pi.add_apply] at hfinal
  rw [_root_.MeasureTheory.integral_add (hmainLp.integrable_sq.const_mul 2) (hduLp.integrable_sq.const_mul (8 * N^2)),
    _root_.MeasureTheory.integral_const_mul, _root_.MeasureTheory.integral_const_mul] at hfinal
  have hind : (∫ x, ((tsupport η).indicator (diffQuot k h u) x)^2) =
      ∫ x in tsupport η, (diffQuot k h u x)^2 := by
    rw [← _root_.MeasureTheory.integral_indicator (isClosed_tsupport η).measurableSet]
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x ∈ tsupport η <;> simp [hx]
  rw [hind] at hfinal
  exact hbound.trans hfinal

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.integral_sq_nirenbergTestFunction_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.integral_sq_nirenbergTestFunction_le target :: scope.openDecls } }

private theorem abs_integral_mul_nirenbergTestFunction_le
    {d : ℕ} {u g η f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : _root_.MeasureTheory.MemLp u 2 _root_.MeasureTheory.MeasureSpace.volume) (hg : _root_.MeasureTheory.MemLp g 2 _root_.MeasureTheory.MeasureSpace.volume) (hf : _root_.MeasureTheory.MemLp f 2 _root_.MeasureTheory.MeasureSpace.volume)
    (k : Fin d) (hweak : DeGiorgi.HasWeakPartialDeriv k g u _root_.Set.univ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηb : ∀ x, |η x| ≤ 1) {N : ℝ}
    (hηd : ∀ x, |fderiv ℝ η x (EuclideanSpace.single k 1)| ≤ N)
    {ε : ℝ} (hε : 0 < ε) (h : ℝ) :
    |∫ x, f x * nirenbergTestFunction k h η u x| ≤
      ε * (∫ x, (η x * diffQuot k h g x)^2) +
      (2 * ε)⁻¹ * (∫ x, f x ^ 2) +
      4 * ε * N^2 * (∫ x in tsupport η, (diffQuot k h u x)^2) := by
  let v := nirenbergTestFunction k h η u
  have hηsqc : HasCompactSupport (fun x => (η x)^2) :=
    hηc.comp_left (g := fun y : ℝ => y^2) (by simp)
  have hηsqLp : _root_.MeasureTheory.MemLp (fun x => (η x)^2) ∞ volume :=
    (hη.pow 2).continuous.memLp_of_hasCompactSupport hηsqc
  have hv : _root_.MeasureTheory.MemLp v 2 volume :=
    memLp_diffQuot_two k (-h) ((memLp_diffQuot_two k h hu).mul' hηsqLp)
  have hp : _root_.MeasureTheory.Integrable (fun x => f x * v x) volume := hf.integrable_mul hv
  have hy : (∫ x, |f x * v x|) ≤
      (ε / 2) * (∫ x, (v x)^2) + (2 * ε)⁻¹ * (∫ x, (f x)^2) := by
    rw [← _root_.MeasureTheory.integral_const_mul, ← _root_.MeasureTheory.integral_const_mul,
      ← _root_.MeasureTheory.integral_add (hv.integrable_sq.const_mul (ε / 2))
        (hf.integrable_sq.const_mul ((2 * ε)⁻¹))]
    apply _root_.MeasureTheory.integral_mono_ae hp.abs
      ((hv.integrable_sq.const_mul (ε / 2)).add (hf.integrable_sq.const_mul ((2 * ε)⁻¹)))
    filter_upwards [] with x
    have hpoint := two_mul_le_add_mul_sq (a := |v x|) (b := |f x|) hε
    rw [sq_abs, sq_abs] at hpoint
    have heq : ε⁻¹ = 2 * (2 * ε)⁻¹ := by
      field_simp
    rw [heq] at hpoint
    rw [abs_mul]
    simp only [Pi.add_apply]
    nlinarith only [hpoint]
  have hn := integral_sq_nirenbergTestFunction_le hu hg k hweak hη hηc hηb hηd h
  have hm := mul_le_mul_of_nonneg_left hn (show 0 ≤ ε / 2 by positivity)
  have habs : |∫ x, f x * v x| ≤ ∫ x, |f x * v x| :=
    _root_.MeasureTheory.abs_integral_le_integral_abs
  change |∫ x, f x * v x| ≤ _
  have h := habs.trans hy
  dsimp only [v] at h
  nlinarith only [h, hm]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.abs_integral_mul_nirenbergTestFunction_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.abs_integral_mul_nirenbergTestFunction_le target :: scope.openDecls } }

private theorem memLp_cutoff_product_local
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    {u χ : EuclideanSpace ℝ (Fin d) → ℝ} (hu : _root_.MeasureTheory.MemLp u 2 (volume.restrict Ω))
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ Ω) :
    MemLp (fun x => χ x * u x) 2 volume := by
  have hm : _root_.MeasureTheory.MemLp (fun x => χ x * u x) 2 (volume.restrict Ω) :=
    hu.mul' ((hχ.memLp_of_hasCompactSupport hχc : _root_.MeasureTheory.MemLp χ ∞ _root_.MeasureTheory.MeasureSpace.volume).restrict Ω)
  have hi := (_root_.MeasureTheory.memLp_indicator_iff_restrict hΩ.measurableSet).mpr hm
  have heq : Ω.indicator (fun x => χ x * u x) = fun x => χ x * u x := by
    funext x
    by_cases hx : x ∈ Ω
    · rw [_root_.Set.indicator_of_mem hx]
    · rw [_root_.Set.indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport (fun hs => hx (hχs hs)), _root_.MulZeroClass.zero_mul]
  rwa [heq] at hi

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.memLp_cutoff_product_local
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.memLp_cutoff_product_local target :: scope.openDecls } }

private theorem exists_lp_weak_partial_extension
    {d : ℕ} {Ω K : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {u g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : _root_.MeasureTheory.MemLp u 2 (volume.restrict Ω)) (hg : _root_.MeasureTheory.MemLp g 2 (volume.restrict Ω))
    (k : Fin d) (hweak : DeGiorgi.HasWeakPartialDeriv k g u Ω) :
    ∃ v w : EuclideanSpace ℝ (Fin d) → ℝ, _root_.MeasureTheory.MemLp v 2 _root_.MeasureTheory.MeasureSpace.volume ∧ _root_.MeasureTheory.MemLp w 2 _root_.MeasureTheory.MeasureSpace.volume ∧
      DeGiorgi.HasWeakPartialDeriv k w v _root_.Set.univ ∧ _root_.Set.EqOn v u K ∧ _root_.Set.EqOn w g K := by
  obtain ⟨δ, χ, hδ, _, hχ, hχc, _, hχone, hχs⟩ :=
    Euclidean.exists_smooth_cutoff_with_neighborhood hK hΩ hKΩ
  let v := fun x => χ x * u x
  let w := fun x => χ x * g x + fderiv ℝ χ x (EuclideanSpace.single k 1) * u x
  have hv : _root_.MeasureTheory.MemLp v 2 volume := memLp_cutoff_product_local hΩ hu hχ.continuous hχc hχs
  have hDχ := (hχ.continuous_fderiv (by simp)).clm_apply
    (continuous_const : Continuous (fun _ : EuclideanSpace ℝ (Fin d) => EuclideanSpace.single k (1 : ℝ)))
  have hw : _root_.MeasureTheory.MemLp w 2 volume :=
    (memLp_cutoff_product_local hΩ hg hχ.continuous hχc hχs).add
      (memLp_cutoff_product_local hΩ hu hDχ (hχc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k 1))
        ((tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single k 1)).trans hχs))
  refine ⟨v, w, hv, hw, hasWeakPartialDeriv_mul_cutoff_univ hΩ hu hg k hweak hχ hχc hχs, ?_, ?_⟩
  · intro x hx
    simp only [v, hχone x (_root_.Metric.self_subset_cthickening K hx), one_mul]
  · intro x hx
    simp only [w, hχone x (_root_.Metric.self_subset_cthickening K hx), one_mul,
      Euclidean.fderiv_cutoff_apply_zero_on_cthickening hδ hχone hx k, _root_.MulZeroClass.zero_mul, add_zero]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.exists_lp_weak_partial_extension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.exists_lp_weak_partial_extension target :: scope.openDecls } }

private theorem diffQuot_eqOn_tsupport
    {d : ℕ} (k : Fin d) (h : ℝ) {η u v : EuclideanSpace ℝ (Fin d) → ℝ}
    (heq : _root_.Set.EqOn u v (_root_.Metric.cthickening |h| (tsupport η))) :
    EqOn (diffQuot k h u) (diffQuot k h v) (tsupport η) := by
  intro x hx
  by_cases hh : h = 0
  · simp only [hh, diffQuot_zero_h, Pi.zero_apply]
  have hbase := heq (_root_.Metric.self_subset_cthickening _ hx)
  have hshift : u (x + h • EuclideanSpace.single k (1 : ℝ)) =
      v (x + h • EuclideanSpace.single k (1 : ℝ)) := by
    apply heq
    apply _root_.Metric.closedBall_subset_cthickening hx |h|
    rw [_root_.Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
    simp only [PiLp.norm_single, _root_.NormOneClass.norm_one, mul_one, Real.norm_eq_abs, le_refl]
  simp only [diffQuot_apply_of_ne k hh, hbase, hshift]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.diffQuot_eqOn_tsupport
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.diffQuot_eqOn_tsupport target :: scope.openDecls } }

theorem integral_sq_nirenbergTestFunction_le_local
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    {u g η : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : _root_.MeasureTheory.MemLp u 2 (volume.restrict Ω)) (hg : _root_.MeasureTheory.MemLp g 2 (volume.restrict Ω))
    (k : Fin d) (hweak : DeGiorgi.HasWeakPartialDeriv k g u Ω)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηb : ∀ x, |η x| ≤ 1) {N : ℝ}
    (hηd : ∀ x, |fderiv ℝ η x (EuclideanSpace.single k 1)| ≤ N)
    (h : ℝ) (hroom : _root_.Metric.cthickening |h| (tsupport η) ⊆ Ω) :
    (∫ x, (nirenbergTestFunction k h η u x)^2) ≤
      2 * (∫ x, (η x * diffQuot k h g x)^2) +
        8 * N^2 * ∫ x in tsupport η, (diffQuot k h u x)^2 := by
  obtain ⟨v, w, hv, hw, hweak', heqv, heqw⟩ :=
    exists_lp_weak_partial_extension hΩ (hηc.cthickening (r := |h|)) hroom hu hg k hweak
  have htest := nirenbergTestFunction_congr_of_eqOn_cthickening k h heqv
  have hmain : (fun x => η x * diffQuot k h w x) = fun x => η x * diffQuot k h g x := by
    funext x
    by_cases hx : x ∈ tsupport η
    · rw [diffQuot_eqOn_tsupport k h heqw hx]
    · rw [image_eq_zero_of_notMem_tsupport hx, _root_.MulZeroClass.zero_mul, _root_.MulZeroClass.zero_mul]
  have hlower : (∫ x in tsupport η, (diffQuot k h v x)^2) =
      ∫ x in tsupport η, (diffQuot k h u x)^2 := by
    apply _root_.MeasureTheory.setIntegral_congr_fun (isClosed_tsupport η).measurableSet
    intro x hx
    exact congrArg (fun r : ℝ => r^2) (diffQuot_eqOn_tsupport k h heqv hx)
  have hb := integral_sq_nirenbergTestFunction_le hv hw k hweak' hη hηc hηb hηd h
  rw [htest, hlower] at hb
  change (∫ x, (nirenbergTestFunction k h η u x)^2) ≤
      2 * (∫ x, ((fun x => η x * diffQuot k h w x) x)^2) + _ at hb
  rw [hmain] at hb
  exact hb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.integral_sq_nirenbergTestFunction_le_local then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.integral_sq_nirenbergTestFunction_le_local"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.integral_sq_nirenbergTestFunction_le_local ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.integral_sq_nirenbergTestFunction_le_local

theorem abs_integral_mul_nirenbergTestFunction_le_local
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    {u g η f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : _root_.MeasureTheory.MemLp u 2 (volume.restrict Ω)) (hg : _root_.MeasureTheory.MemLp g 2 (volume.restrict Ω))
    (hf : _root_.MeasureTheory.MemLp f 2 (volume.restrict Ω))
    (k : Fin d) (hweak : DeGiorgi.HasWeakPartialDeriv k g u Ω)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηb : ∀ x, |η x| ≤ 1) {N : ℝ}
    (hηd : ∀ x, |fderiv ℝ η x (EuclideanSpace.single k 1)| ≤ N)
    {ε : ℝ} (hε : 0 < ε) (h : ℝ) (hroom : _root_.Metric.cthickening |h| (tsupport η) ⊆ Ω) :
    |∫ x in Ω, f x * nirenbergTestFunction k h η u x| ≤
      ε * (∫ x, (η x * diffQuot k h g x)^2) +
      (2 * ε)⁻¹ * (∫ x in Ω, f x ^ 2) +
      4 * ε * N^2 * (∫ x in tsupport η, (diffQuot k h u x)^2) := by
  obtain ⟨v, w, hv, hw, hweak', heqv, heqw⟩ :=
    exists_lp_weak_partial_extension hΩ (hηc.cthickening (r := |h|)) hroom hu hg k hweak
  have htest := nirenbergTestFunction_congr_of_eqOn_cthickening k h heqv
  have hmain : (fun x => η x * diffQuot k h w x) = fun x => η x * diffQuot k h g x := by
    funext x
    by_cases hx : x ∈ tsupport η
    · rw [diffQuot_eqOn_tsupport k h heqw hx]
    · rw [image_eq_zero_of_notMem_tsupport hx, _root_.MulZeroClass.zero_mul, _root_.MulZeroClass.zero_mul]
  have hlower : (∫ x in tsupport η, (diffQuot k h v x)^2) =
      ∫ x in tsupport η, (diffQuot k h u x)^2 := by
    apply _root_.MeasureTheory.setIntegral_congr_fun (isClosed_tsupport η).measurableSet
    intro x hx
    exact congrArg (fun r : ℝ => r^2) (diffQuot_eqOn_tsupport k h heqv hx)
  have hfglobal : _root_.MeasureTheory.MemLp (Ω.indicator f) 2 volume :=
    (_root_.MeasureTheory.memLp_indicator_iff_restrict hΩ.measurableSet).mpr hf
  have hb := abs_integral_mul_nirenbergTestFunction_le hv hw hfglobal k hweak' hη hηc hηb hηd hε h
  rw [htest, hlower] at hb
  change |∫ x, Ω.indicator f x * nirenbergTestFunction k h η u x| ≤
    (ε * (∫ x, ((fun x => η x * diffQuot k h w x) x)^2) + _) + _ at hb
  rw [hmain] at hb
  have hforce : (∫ x, Ω.indicator f x * nirenbergTestFunction k h η u x) =
      ∫ x in Ω, f x * nirenbergTestFunction k h η u x := by
    rw [← _root_.MeasureTheory.integral_indicator hΩ.measurableSet]
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x ∈ Ω <;> simp [hx]
  have hforceSq : (∫ x, (Ω.indicator f x)^2) = ∫ x in Ω, (f x)^2 := by
    rw [← _root_.MeasureTheory.integral_indicator hΩ.measurableSet]
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x ∈ Ω <;> simp [hx]
  rwa [hforce, hforceSq] at hb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.abs_integral_mul_nirenbergTestFunction_le_local then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.abs_integral_mul_nirenbergTestFunction_le_local"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.abs_integral_mul_nirenbergTestFunction_le_local ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.abs_integral_mul_nirenbergTestFunction_le_local

end DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
