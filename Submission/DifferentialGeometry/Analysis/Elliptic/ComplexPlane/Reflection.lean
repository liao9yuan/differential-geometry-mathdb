import Submission.DifferentialGeometry.Analysis.Integration.Integral.HalfPlaneLaplacian
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.MetricSpace.Holder

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.MeasureTheory _root_.Set _root_.Filter _root_.InnerProductSpace _root_.Submission.InnerProductSpace
open scoped _root_.Topology _root_.ContDiff _root_.NNReal
namespace DifferentialGeometry.Analysis

def oddReflection {F : Type*} [AddGroup F] (f : ℂ → F) : ℂ → F :=
  {z : ℂ | 0 < z.im}.indicator f - {z : ℂ | z.im < 0}.indicator (f ∘ Complex.conjLIE)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.oddReflection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.oddReflection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.oddReflection ``Submission.DifferentialGeometry.Analysis.oddReflection

theorem oddReflection_of_im_pos {F : Type*} [AddGroup F] (f : ℂ → F)
    {z : ℂ} (hz : 0 < z.im) : oddReflection f z = f z := by
  simp [oddReflection, hz, not_lt_of_ge hz.le]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.oddReflection_of_im_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.oddReflection_of_im_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.oddReflection_of_im_pos ``Submission.DifferentialGeometry.Analysis.oddReflection_of_im_pos

theorem oddReflection_of_im_neg {F : Type*} [AddGroup F] (f : ℂ → F)
    {z : ℂ} (hz : z.im < 0) : oddReflection f z = -f (Complex.conjLIE z) := by
  simp [oddReflection, hz, not_lt_of_ge hz.le, Function.comp_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.oddReflection_of_im_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.oddReflection_of_im_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.oddReflection_of_im_neg ``Submission.DifferentialGeometry.Analysis.oddReflection_of_im_neg

theorem oddReflection_of_im_zero {F : Type*} [AddGroup F] (f : ℂ → F)
    {z : ℂ} (hz : z.im = 0) : oddReflection f z = 0 := by
  simp [oddReflection, hz]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.oddReflection_of_im_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.oddReflection_of_im_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.oddReflection_of_im_zero ``Submission.DifferentialGeometry.Analysis.oddReflection_of_im_zero

theorem oddReflection_conj {F : Type*} [AddGroup F] (f : ℂ → F) (z : ℂ) :
    oddReflection f (Complex.conjLIE z) = -oddReflection f z := by
  have hi : (Complex.conjLIE z).im = -z.im := Complex.conj_im z
  have hinv : Complex.conjLIE (Complex.conjLIE z) = z := starRingEnd_self_apply z
  rcases lt_trichotomy (0 : ℝ) z.im with hp | hz | hn
  · rw [oddReflection_of_im_neg f (by rw [hi]; linarith), hinv, oddReflection_of_im_pos f hp]
  · rw [oddReflection_of_im_zero f hz.symm, oddReflection_of_im_zero f (by rw [hi, hz.symm, neg_zero]), neg_zero]
  · rw [oddReflection_of_im_pos f (by rw [hi]; linarith), oddReflection_of_im_neg f hn, neg_neg]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.oddReflection_conj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.oddReflection_conj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.oddReflection_conj ``Submission.DifferentialGeometry.Analysis.oddReflection_conj

theorem oddReflection_eq_of_im_nonneg {F : Type*} [AddGroup F] (f : ℂ → F)
    (hzero : ∀ z : ℂ, z.im = 0 → f z = 0) {z : ℂ} (hz : 0 ≤ z.im) :
    oddReflection f z = f z := by
  rcases hz.eq_or_lt with hz | hz
  · rw [oddReflection_of_im_zero f hz.symm, hzero z hz.symm]
  · exact oddReflection_of_im_pos f hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.oddReflection_eq_of_im_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.oddReflection_eq_of_im_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.oddReflection_eq_of_im_nonneg ``Submission.DifferentialGeometry.Analysis.oddReflection_eq_of_im_nonneg

theorem hasCompactSupport_oddReflection {F : Type*} [AddGroup F] {f : ℂ → F}
    (hc : HasCompactSupport f) : HasCompactSupport (oddReflection f) := by
  have hi (g : ℂ → F) (s : Set ℂ) (hg : HasCompactSupport g) :
      HasCompactSupport (s.indicator g) := by
    apply HasCompactSupport.intro hg
    intro z hz
    simp [_root_.Set.indicator, image_eq_zero_of_notMem_tsupport hz]
  exact (hi f _ hc).sub (hi _ _ (hc.comp_homeomorph Complex.conjLIE.toHomeomorph))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.hasCompactSupport_oddReflection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.hasCompactSupport_oddReflection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.hasCompactSupport_oddReflection ``Submission.DifferentialGeometry.Analysis.hasCompactSupport_oddReflection

theorem oddReflection_norm_le
    {F : Type*} [NormedAddCommGroup F] {f : ℂ → F} {K : ℝ}
    (hg : ∀ z : ℂ, 0 < z.im → ‖f z‖ ≤ K * z.im) (z : ℂ) :
    ‖oddReflection f z‖ ≤ K * |z.im| := by
  rcases lt_trichotomy (0 : ℝ) z.im with hp | hz | hn
  · rw [oddReflection_of_im_pos f hp, abs_of_pos hp]
    exact hg z hp
  · rw [oddReflection_of_im_zero f hz.symm, norm_zero, hz.symm, abs_zero, _root_.MulZeroClass.mul_zero]
  · rw [oddReflection_of_im_neg f hn, norm_neg, abs_of_neg hn]
    simpa only [Complex.conjLIE_apply, Complex.conj_im] using
      hg (Complex.conjLIE z) (by simpa only [Complex.conjLIE_apply, Complex.conj_im, neg_pos] using hn)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.oddReflection_norm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.oddReflection_norm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.oddReflection_norm_le ``Submission.DifferentialGeometry.Analysis.oddReflection_norm_le

theorem continuous_oddReflection_of_norm_le_mul_im
    {F : Type*} [NormedAddCommGroup F] {f : ℂ → F} {K : ℝ}
    (hf : ContinuousOn f {z : ℂ | 0 < z.im})
    (hg : ∀ z : ℂ, 0 < z.im → ‖f z‖ ≤ K * z.im) :
    Continuous (oddReflection f) := by
  have hU : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  apply continuous_iff_continuousAt.mpr
  intro z
  rcases lt_trichotomy (0 : ℝ) z.im with hp | hz | hn
  · have he : oddReflection f =ᶠ[𝓝 z] f := by
      filter_upwards [hU.mem_nhds hp] with w hw
      exact oddReflection_of_im_pos f hw
    exact (continuousAt_congr he).mpr ((hf z hp).continuousAt (hU.mem_nhds hp))
  · rw [ContinuousAt, oddReflection_of_im_zero f hz.symm]
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hlim : _root_.Filter.Tendsto (fun w : ℂ => K * |w.im|) (𝓝 z) (𝓝 0) := by
      have hh : Continuous (fun w : ℂ => K * |w.im|) :=
        continuous_const.mul Complex.continuous_im.abs
      simpa only [ContinuousAt, hz.symm, abs_zero, _root_.MulZeroClass.mul_zero] using hh.continuousAt (x := z)
    exact squeeze_zero (fun w => norm_nonneg _) (oddReflection_norm_le hg) hlim
  · have hcz : 0 < (Complex.conjLIE z).im := by
      simpa only [Complex.conjLIE_apply, Complex.conj_im, neg_pos] using hn
    have he : oddReflection f =ᶠ[𝓝 z] fun w => -f (Complex.conjLIE w) := by
      filter_upwards [(isOpen_lt Complex.continuous_im continuous_const).mem_nhds hn] with w hw
      exact oddReflection_of_im_neg f hw
    exact (continuousAt_congr he).mpr
      (((hf (Complex.conjLIE z) hcz).continuousAt (hU.mem_nhds hcz)).comp
        Complex.conjLIE.continuous.continuousAt).neg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.continuous_oddReflection_of_norm_le_mul_im then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.continuous_oddReflection_of_norm_le_mul_im"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.continuous_oddReflection_of_norm_le_mul_im ``Submission.DifferentialGeometry.Analysis.continuous_oddReflection_of_norm_le_mul_im

private theorem integral_indicator_add_indicator_comp_conj
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : ℂ → F}
    (hf : _root_.MeasureTheory.IntegrableOn f {z : ℂ | 0 < z.im})
    (hg : _root_.MeasureTheory.IntegrableOn g {z : ℂ | 0 < z.im}) :
    (∫ z : ℂ, {z : ℂ | 0 < z.im}.indicator f z +
      {z : ℂ | z.im < 0}.indicator (g ∘ Complex.conjLIE) z) =
      ∫ z in {z : ℂ | 0 < z.im}, f z + g z := by
  have hU : MeasurableSet {z : ℂ | 0 < z.im} :=
    (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  have hL : MeasurableSet {z : ℂ | z.im < 0} :=
    (isOpen_lt Complex.continuous_im continuous_const).measurableSet
  have hp : Complex.conjLIE ⁻¹' {z : ℂ | z.im < 0} = {z : ℂ | 0 < z.im} := by
    ext z
    simp only [_root_.Set.mem_preimage, _root_.Set.mem_ofPred_eq, Complex.conjLIE_apply, Complex.conj_im, neg_lt_zero]
  have hpres := Complex.conjLIE.measurePreserving
  have hemb : MeasurableEmbedding (Complex.conjLIE : ℂ → ℂ) :=
    Complex.conjLIE.toHomeomorph.isClosedEmbedding.measurableEmbedding
  have hinv (z : ℂ) : Complex.conjLIE (Complex.conjLIE z) = z := starRingEnd_self_apply z
  have hlow : _root_.MeasureTheory.IntegrableOn (g ∘ Complex.conjLIE) {z : ℂ | z.im < 0} := by
    apply (hpres.integrableOn_comp_preimage hemb).mp
    simpa only [hp, Function.comp_def, hinv] using hg
  rw [_root_.MeasureTheory.integral_add ((_root_.MeasureTheory.integrable_indicator_iff hU).mpr hf)
    ((_root_.MeasureTheory.integrable_indicator_iff hL).mpr hlow), _root_.MeasureTheory.integral_indicator hU, _root_.MeasureTheory.integral_indicator hL]
  have hchange := hpres.setIntegral_preimage_emb hemb
    (g ∘ Complex.conjLIE) {z : ℂ | z.im < 0}
  simp only [hp, Function.comp_apply, hinv] at hchange
  change (∫ z in {z : ℂ | 0 < z.im}, f z) +
    (∫ z in {z : ℂ | z.im < 0}, g (Complex.conjLIE z)) = _
  rw [← hchange, ← _root_.MeasureTheory.integral_add hf hg]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.integral_indicator_add_indicator_comp_conj
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.integral_indicator_add_indicator_comp_conj target :: scope.openDecls } }

theorem oddReflection_congr {F : Type*} [AddGroup F] {f g : ℂ → F}
    (hfg : _root_.Set.EqOn f g {z : ℂ | 0 < z.im}) : oddReflection f = oddReflection g := by
  funext z
  rcases lt_trichotomy (0 : ℝ) z.im with hp | hz | hn
  · rw [oddReflection_of_im_pos f hp, oddReflection_of_im_pos g hp, hfg hp]
  · rw [oddReflection_of_im_zero f hz.symm, oddReflection_of_im_zero g hz.symm]
  · rw [oddReflection_of_im_neg f hn, oddReflection_of_im_neg g hn,
      hfg (by simpa using hn)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.oddReflection_congr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.oddReflection_congr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.oddReflection_congr ``Submission.DifferentialGeometry.Analysis.oddReflection_congr

private theorem oddReflection_eq_neg_of_im_nonpos
    {F : Type*} [AddGroup F] {f : ℂ → F}
    (hzero : ∀ z : ℂ, z.im = 0 → f z = 0) {z : ℂ} (hz : z.im ≤ 0) :
    oddReflection f z = -f (Complex.conjLIE z) := by
  calc
    oddReflection f z = -oddReflection f (Complex.conjLIE z) := by
      rw [oddReflection_conj, neg_neg]
    _ = -f (Complex.conjLIE z) := by
      rw [oddReflection_eq_of_im_nonneg f hzero (by simpa using hz)]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.oddReflection_eq_neg_of_im_nonpos
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.oddReflection_eq_neg_of_im_nonpos target :: scope.openDecls } }

theorem holderWith_oddReflection
    {F : Type*} [NormedAddCommGroup F] {f : ℂ → F} {K α : ℝ≥0}
    (hf : HolderOnWith K α f {z : ℂ | 0 ≤ z.im})
    (hzero : ∀ z : ℂ, z.im = 0 → f z = 0) :
    HolderWith (2 * K) α (oddReflection f) := by
  have hnorm {z : ℂ} (hz : 0 ≤ z.im) {d : ℝ} (hd : |z.im| ≤ d) :
      ‖f z‖ ≤ K * d ^ (α : ℝ) := by
    have hdist : _root_.Dist.dist z (z.re : ℂ) = |z.im| := by
      rw [dist_eq_norm]
      have he : z - (z.re : ℂ) = (z.im : ℂ) * Complex.I := by
        apply Complex.ext <;> simp
      rw [he, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hh := hf.dist_le_of_le hz (show (z.re : ℂ) ∈ {w : ℂ | 0 ≤ w.im} from by simp)
      (hdist.trans_le hd)
    simpa only [hzero (z.re : ℂ) (by simp), dist_zero_right] using hh
  have hcross {z w : ℂ} (hz : 0 ≤ z.im) (hw : w.im ≤ 0) :
      dist (oddReflection f z) (oddReflection f w) ≤ (2 * K : ℝ≥0) * _root_.Dist.dist z w ^ (α : ℝ) := by
    have hdiff : z.im - w.im ≤ _root_.Dist.dist z w := by
      have hh := Complex.abs_im_le_norm (z - w)
      rw [Complex.sub_im, abs_of_nonneg (sub_nonneg.mpr (hw.trans hz))] at hh
      simpa only [dist_eq_norm] using hh
    have hzdist : |z.im| ≤ _root_.Dist.dist z w := by rw [abs_of_nonneg hz]; linarith
    have hwdist : |(Complex.conjLIE w).im| ≤ _root_.Dist.dist z w := by
      simp only [Complex.conjLIE_apply, Complex.conj_im, abs_neg, abs_of_nonpos hw]
      linarith
    rw [oddReflection_eq_of_im_nonneg f hzero hz,
      oddReflection_eq_neg_of_im_nonpos hzero hw, dist_eq_norm, sub_neg_eq_add]
    exact (norm_add_le _ _).trans (by
      have h1 := hnorm hz hzdist
      have h2 := hnorm (z := Complex.conjLIE w) (by simpa using hw) hwdist
      simp only [NNReal.coe_mul, NNReal.coe_ofNat]
      linarith)
  have hsame {z w : ℂ} (hz : 0 ≤ z.im) (hw : 0 ≤ w.im) :
      dist (f z) (f w) ≤ (2 * K : ℝ≥0) * _root_.Dist.dist z w ^ (α : ℝ) := by
    apply (hf.dist_le hz hw).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (dist_nonneg) _)
    simp only [NNReal.coe_mul, NNReal.coe_ofNat]
    linarith [K.coe_nonneg]
  intro z w
  rw [edist_nndist, edist_nndist, ← ENNReal.coe_rpow_of_nonneg _ α.coe_nonneg,
    ← ENNReal.coe_mul, ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
  simp only [coe_nndist, NNReal.coe_mul, NNReal.coe_rpow, NNReal.coe_ofNat]
  rcases le_total 0 z.im with hz | hz <;> rcases le_total 0 w.im with hw | hw
  · rw [oddReflection_eq_of_im_nonneg f hzero hz, oddReflection_eq_of_im_nonneg f hzero hw]
    exact hsame hz hw
  · exact hcross hz hw
  · simpa only [dist_comm, NNReal.coe_mul, NNReal.coe_ofNat] using hcross hw hz
  · rw [oddReflection_eq_neg_of_im_nonpos hzero hz,
      oddReflection_eq_neg_of_im_nonpos hzero hw, dist_neg_neg]
    have hh := hsame (z := Complex.conjLIE z) (w := Complex.conjLIE w)
      (by simpa using hz) (by simpa using hw)
    simpa only [Complex.conjLIE.isometry.dist_eq, NNReal.coe_mul, NNReal.coe_ofNat] using hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.holderWith_oddReflection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.holderWith_oddReflection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.holderWith_oddReflection ``Submission.DifferentialGeometry.Analysis.holderWith_oddReflection

private theorem integral_smul_oddReflection
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : ℂ → ℝ} {f : ℂ → F}
    (h₁ : _root_.MeasureTheory.IntegrableOn (fun z => φ z • f z) {z : ℂ | 0 < z.im})
    (h₂ : _root_.MeasureTheory.IntegrableOn (fun z => φ (Complex.conjLIE z) • f z) {z : ℂ | 0 < z.im}) :
    ∫ z : ℂ, φ z • oddReflection f z =
      ∫ z in {z : ℂ | 0 < z.im}, (φ z - φ (Complex.conjLIE z)) • f z := by
  have he (z : ℂ) : φ z • oddReflection f z =
      {z : ℂ | 0 < z.im}.indicator (fun z => φ z • f z) z +
      {z : ℂ | z.im < 0}.indicator ((fun z => -(φ (Complex.conjLIE z) • f z)) ∘ Complex.conjLIE) z := by
    by_cases hi : 0 < z.im <;> by_cases hl : z.im < 0 <;>
      simp [oddReflection, _root_.Set.indicator, hi, hl, Function.comp_apply, sub_eq_add_neg]
  simp_rw [he]
  rw [integral_indicator_add_indicator_comp_conj
    (g := fun z => -(φ (Complex.conjLIE z) • f z)) h₁ h₂.neg]
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards with z
  rw [sub_smul, sub_eq_add_neg]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.integral_smul_oddReflection
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.integral_smul_oddReflection target :: scope.openDecls } }


private theorem integrableOn_smul_of_bound_on_tsupport
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : ℂ → ℝ} {f : ℂ → F} {s : Set ℂ} {B : ℝ}
    (hs : MeasurableSet s) (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (hf : ContinuousOn f s)
    (hB : ∀ z ∈ tsupport φ, z ∈ s → ‖f z‖ ≤ B) :
    IntegrableOn (fun z => φ z • f z) s := by
  obtain ⟨A, hA⟩ := hc.exists_bound_of_continuousOn hφ.continuousOn
  apply (_root_.MeasureTheory.integrableOn_iff_integrable_of_support_subset
    ((Function.support_smul_subset_left φ f).trans (subset_tsupport φ))).mp
  apply IntegrableOn.of_bound ((Measure.restrict_le_self _).trans_lt hc.measure_lt_top)
    ((hφ.continuousOn.smul hf).aestronglyMeasurable hs).restrict (_root_.Max.max A 0 * _root_.Max.max B 0)
  filter_upwards [_root_.MeasureTheory.ae_restrict_mem (isClosed_tsupport φ).measurableSet,
    _root_.MeasureTheory.ae_restrict_of_ae (_root_.MeasureTheory.ae_restrict_mem hs)] with z hz hzs
  change ‖φ z • f z‖ ≤ _
  rw [norm_smul]
  exact mul_le_mul ((hA z hz).trans (le_max_left _ _))
    ((hB z hz hzs).trans (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.integrableOn_smul_of_bound_on_tsupport
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.integrableOn_smul_of_bound_on_tsupport target :: scope.openDecls } }

private theorem integrableOn_smul_of_linear_growth
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : ℂ → ℝ} {f : ℂ → F} {K : ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (hf : ContinuousOn f {z : ℂ | 0 < z.im})
    (hg : ∀ z : ℂ, 0 < z.im → ‖f z‖ ≤ K * z.im) :
    IntegrableOn (fun z => φ z • f z) {z : ℂ | 0 < z.im} := by
  obtain ⟨R, hR⟩ := hc.exists_bound_of_continuousOn Complex.continuous_im.continuousOn
  apply integrableOn_smul_of_bound_on_tsupport
    (isOpen_lt continuous_const Complex.continuous_im).measurableSet hφ hc hf (B := _root_.Max.max K 0 * _root_.Max.max R 0)
  intro z hz hzs
  exact (hg z hzs).trans (mul_le_mul (le_max_left _ _)
    ((le_abs_self _).trans ((hR z hz).trans (le_max_left _ _))) hzs.le (le_max_right _ _))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.integrableOn_smul_of_linear_growth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.integrableOn_smul_of_linear_growth target :: scope.openDecls } }

theorem integral_laplacian_smul_oddReflection
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : ℂ → ℝ} {f : ℂ → F} {K B : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hf : ∀ z : ℂ, 0 < z.im → ContDiffAt ℝ 2 f z)
    (hg : ∀ z : ℂ, 0 < z.im → ‖f z‖ ≤ K * z.im)
    (hB : ∀ z : ℂ, 0 < z.im → ‖Laplacian.laplacian f z‖ ≤ B) :
    ∫ z : ℂ, Laplacian.laplacian φ z • oddReflection f z =
      ∫ z : ℂ, φ z • oddReflection (Laplacian.laplacian f) z := by
  let ψ : ℂ → ℝ := fun z => φ z - φ (Complex.conjLIE z)
  have he : ContDiff ℝ 2 (Complex.conjLIE : ℂ → ℂ) :=
    Complex.conjCLE.contDiff
  have hψ : ContDiff ℝ 2 ψ := hφ.sub (hφ.comp he)
  have hcψ : HasCompactSupport ψ := hc.sub (hc.comp_homeomorph Complex.conjLIE.toHomeomorph)
  have hψ0 (z : ℂ) (hz : z.im = 0) : ψ z = 0 := by
    have hcj : Complex.conjLIE z = z := Complex.conj_eq_iff_im.mpr hz
    simp only [ψ, hcj, sub_self]
  have hψΔ (z : ℂ) : Laplacian.laplacian ψ z =
      Laplacian.laplacian φ z - Laplacian.laplacian φ (Complex.conjLIE z) := by
    change Laplacian.laplacian (φ - φ ∘ Complex.conjLIE) z = _
    rw [hφ.contDiffAt.laplacian_sub (hφ.comp he).contDiffAt]
    rw [Complex.conjLIE.laplacian_comp φ]
  have hfc : ContinuousOn f {z : ℂ | 0 < z.im} :=
    fun z hz => (hf z hz).continuousAt.continuousWithinAt
  have hΔc : ContinuousOn (Laplacian.laplacian f) {z : ℂ | 0 < z.im} := by
    exact fun z hz => (hf z hz).continuousAt_laplacian.continuousWithinAt
  have hcΔ : HasCompactSupport (Laplacian.laplacian φ) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_laplacian_subset φ)
  have hΔφc := continuous_laplacian hφ
  rw [integral_smul_oddReflection
      (integrableOn_smul_of_linear_growth hΔφc hcΔ hfc hg)
      (integrableOn_smul_of_linear_growth (hΔφc.comp Complex.conjLIE.continuous)
        (hcΔ.comp_homeomorph Complex.conjLIE.toHomeomorph) hfc hg)]
  have hU : MeasurableSet {z : ℂ | 0 < z.im} :=
    (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  rw [integral_smul_oddReflection
      (integrableOn_smul_of_bound_on_tsupport hU hφ.continuous hc hΔc (fun z _ hz => hB z hz))
      (integrableOn_smul_of_bound_on_tsupport hU (hφ.continuous.comp Complex.conjLIE.continuous)
        (hc.comp_homeomorph Complex.conjLIE.toHomeomorph) hΔc (fun z _ hz => hB z hz))]
  have hgreen := integral_smul_laplacian_eq_integral_laplacian_smul_upper_half_plane_of_norm_laplacian_le
    (μ := _root_.MeasureTheory.MeasureSpace.volume) hψ hcψ hψ0 hf (fun z _ hz => hg z hz) (fun z _ hz => hB z hz)
  simpa only [hψΔ] using hgreen.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integral_laplacian_smul_oddReflection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integral_laplacian_smul_oddReflection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integral_laplacian_smul_oddReflection ``Submission.DifferentialGeometry.Analysis.integral_laplacian_smul_oddReflection

theorem oddReflection_norm_le_of_bound
    {F : Type*} [NormedAddCommGroup F] {f : ℂ → F} {B : ℝ}
    (hB : ∀ z : ℂ, 0 < z.im → ‖f z‖ ≤ B) (z : ℂ) :
    ‖oddReflection f z‖ ≤ B := by
  have hB0 : 0 ≤ B := (norm_nonneg (f Complex.I)).trans (hB Complex.I (by simp))
  rcases lt_trichotomy (0 : ℝ) z.im with hp | hz | hn
  · rw [oddReflection_of_im_pos f hp]
    exact hB z hp
  · rw [oddReflection_of_im_zero f hz.symm, norm_zero]
    exact hB0
  · rw [oddReflection_of_im_neg f hn, norm_neg]
    apply hB
    simpa only [Complex.conjLIE_apply, Complex.conj_im, neg_pos] using hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.oddReflection_norm_le_of_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.oddReflection_norm_le_of_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.oddReflection_norm_le_of_bound ``Submission.DifferentialGeometry.Analysis.oddReflection_norm_le_of_bound

theorem aestronglyMeasurable_oddReflection
    {F : Type*} [NormedAddCommGroup F] {f : ℂ → F} {μ : _root_.MeasureTheory.Measure ℂ}
    (hf : ContinuousOn f {z : ℂ | 0 < z.im}) :
    AEStronglyMeasurable (oddReflection f) μ := by
  have hU : MeasurableSet {z : ℂ | 0 < z.im} :=
    (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  have hL : MeasurableSet {z : ℂ | z.im < 0} :=
    (isOpen_lt Complex.continuous_im continuous_const).measurableSet
  have hc : ContinuousOn (f ∘ Complex.conjLIE) {z : ℂ | z.im < 0} :=
    hf.comp Complex.conjLIE.continuous.continuousOn (fun z hz => by
      simpa only [_root_.Set.mem_ofPred_eq, Complex.conjLIE_apply, Complex.conj_im, neg_pos] using hz)
  exact ((aestronglyMeasurable_indicator_iff hU).mpr (hf.aestronglyMeasurable hU)).sub
    ((aestronglyMeasurable_indicator_iff hL).mpr (hc.aestronglyMeasurable hL))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.aestronglyMeasurable_oddReflection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.aestronglyMeasurable_oddReflection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.aestronglyMeasurable_oddReflection ``Submission.DifferentialGeometry.Analysis.aestronglyMeasurable_oddReflection

def evenReflection {F : Type*} (f : ℂ → F) (z : ℂ) : F := f ⟨z.re, |z.im|⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.evenReflection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.evenReflection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.evenReflection ``Submission.DifferentialGeometry.Analysis.evenReflection

theorem evenReflection_of_im_nonneg {F : Type*} (f : ℂ → F)
    {z : ℂ} (hz : 0 ≤ z.im) : evenReflection f z = f z := by
  unfold evenReflection
  congr 1
  exact Complex.ext rfl (abs_of_nonneg hz)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.evenReflection_of_im_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.evenReflection_of_im_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.evenReflection_of_im_nonneg ``Submission.DifferentialGeometry.Analysis.evenReflection_of_im_nonneg

theorem evenReflection_of_im_nonpos {F : Type*} (f : ℂ → F)
    {z : ℂ} (hz : z.im ≤ 0) : evenReflection f z = f (Complex.conjLIE z) := by
  unfold evenReflection
  congr 1
  exact Complex.ext rfl (abs_of_nonpos hz)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.evenReflection_of_im_nonpos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.evenReflection_of_im_nonpos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.evenReflection_of_im_nonpos ``Submission.DifferentialGeometry.Analysis.evenReflection_of_im_nonpos

theorem evenReflection_conj {F : Type*} (f : ℂ → F) (z : ℂ) :
    evenReflection f (Complex.conjLIE z) = evenReflection f z := by
  simp [evenReflection, Complex.conjLIE_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.evenReflection_conj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.evenReflection_conj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.evenReflection_conj ``Submission.DifferentialGeometry.Analysis.evenReflection_conj

theorem continuous_evenReflection {F : Type*} [TopologicalSpace F] {f : ℂ → F}
    (hf : ContinuousOn f {z : ℂ | 0 ≤ z.im}) : Continuous (evenReflection f) := by
  exact hf.comp_continuous
    (by
      have he : (fun z : ℂ => (⟨z.re, |z.im|⟩ : ℂ)) =
          fun z => (z.re : ℂ) + ((|z.im| : ℝ) : ℂ) * Complex.I := by
        funext z
        apply Complex.ext <;> simp
      rw [he]
      fun_prop) (fun z => abs_nonneg z.im)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.continuous_evenReflection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.continuous_evenReflection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.continuous_evenReflection ``Submission.DifferentialGeometry.Analysis.continuous_evenReflection

theorem holderWith_evenReflection {F : Type*} [PseudoEMetricSpace F] {f : ℂ → F}
    {K α : ℝ≥0} (hf : HolderOnWith K α f {z : ℂ | 0 ≤ z.im}) :
    HolderWith K α (evenReflection f) := by
  have hl : LipschitzWith 1 (fun z : ℂ => (⟨z.re, |z.im|⟩ : ℂ)) := by
    apply LipschitzWith.mk_one
    intro z w
    rw [dist_eq_norm, dist_eq_norm]
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    have h := (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr
      (abs_abs_sub_abs_le_abs_sub z.im w.im)
    simp only [sq_abs] at h
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    nlinarith
  change HolderWith K α (fun z : ℂ => f ⟨z.re, |z.im|⟩)
  simpa only [Function.comp_def, one_mul, mul_one, NNReal.one_rpow] using
    hf.comp_holderWith hl.holderWith (fun z => abs_nonneg z.im)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.holderWith_evenReflection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.holderWith_evenReflection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.holderWith_evenReflection ``Submission.DifferentialGeometry.Analysis.holderWith_evenReflection

theorem hasCompactSupport_evenReflection {F : Type*} [Zero F] {f : ℂ → F}
    (hc : HasCompactSupport f) : HasCompactSupport (evenReflection f) := by
  apply HasCompactSupport.intro (hc.union
    (Complex.conjLIE.toHomeomorph.isCompact_preimage.mpr hc))
  intro z hz
  have hz1 : z ∉ tsupport f := fun h => hz (Or.inl h)
  have hz2 : Complex.conjLIE z ∉ tsupport f := fun h => hz (Or.inr h)
  rcases le_total 0 z.im with hp | hn
  · rw [evenReflection_of_im_nonneg f hp, image_eq_zero_of_notMem_tsupport hz1]
  · rw [evenReflection_of_im_nonpos f hn, image_eq_zero_of_notMem_tsupport hz2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.hasCompactSupport_evenReflection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.hasCompactSupport_evenReflection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.hasCompactSupport_evenReflection ``Submission.DifferentialGeometry.Analysis.hasCompactSupport_evenReflection

private theorem ae_im_ne_zero : ∀ᵐ z : ℂ ∂volume, z.im ≠ 0 := by
  have h : ∀ᵐ p : ℝ × ℝ ∂(volume.prod _root_.MeasureTheory.MeasureSpace.volume), p.2 ≠ 0 := by
    apply (Measure.ae_prod_iff_ae_ae (measurable_snd (_root_.MeasurableSingletonClass.measurableSet_singleton 0).compl)).mpr
    filter_upwards with x
    simp [_root_.MeasureTheory.ae_iff, _root_.MeasureTheory.NullSingletonClass.measure_singleton]
  exact Complex.volume_preserving_equiv_real_prod.quasiMeasurePreserving.ae h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.ae_im_ne_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.ae_im_ne_zero target :: scope.openDecls } }

theorem evenReflection_congr_ae {F : Type*} {f g : ℂ → F}
    (hfg : _root_.Set.EqOn f g {z : ℂ | 0 < z.im}) : evenReflection f =ᵐ[_root_.MeasureTheory.MeasureSpace.volume] evenReflection g := by
  filter_upwards [ae_im_ne_zero] with z hz
  rcases lt_or_gt_of_ne hz with hn | hp
  · rw [evenReflection_of_im_nonpos f hn.le, evenReflection_of_im_nonpos g hn.le]
    exact hfg (by simpa using hn)
  · rw [evenReflection_of_im_nonneg f hp.le, evenReflection_of_im_nonneg g hp.le]
    exact hfg hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.evenReflection_congr_ae then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.evenReflection_congr_ae"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.evenReflection_congr_ae ``Submission.DifferentialGeometry.Analysis.evenReflection_congr_ae

private theorem integral_smul_evenReflection
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : ℂ → ℝ} {f : ℂ → F}
    (h₁ : _root_.MeasureTheory.IntegrableOn (fun z => φ z • f z) {z : ℂ | 0 < z.im})
    (h₂ : _root_.MeasureTheory.IntegrableOn (fun z => φ (Complex.conjLIE z) • f z) {z : ℂ | 0 < z.im}) :
    ∫ z : ℂ, φ z • evenReflection f z =
      ∫ z in {z : ℂ | 0 < z.im}, (φ z + φ (Complex.conjLIE z)) • f z := by
  have he : (fun z => φ z • evenReflection f z) =ᵐ[_root_.MeasureTheory.MeasureSpace.volume]
      (fun z => {z : ℂ | 0 < z.im}.indicator (fun z => φ z • f z) z +
      {z : ℂ | z.im < 0}.indicator ((fun z => φ (Complex.conjLIE z) • f z) ∘ Complex.conjLIE) z) := by
    filter_upwards [ae_im_ne_zero] with z hz
    rcases lt_or_gt_of_ne hz with hn | hp
    · simp [evenReflection_of_im_nonpos f hn.le, _root_.Set.indicator, hn, not_lt_of_ge hn.le, Function.comp_apply]
    · simp [evenReflection_of_im_nonneg f hp.le, _root_.Set.indicator, hp, not_lt_of_ge hp.le]
  rw [_root_.MeasureTheory.integral_congr_ae he, integral_indicator_add_indicator_comp_conj h₁ h₂]
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards with z
  rw [add_smul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.integral_smul_evenReflection
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.integral_smul_evenReflection target :: scope.openDecls } }

theorem integral_laplacian_smul_evenReflection
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {φ : ℂ → ℝ} {f : ℂ → F}
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hf : ContDiffOn ℝ 1 f {z : ℂ | 0 ≤ z.im})
    (hf2 : ContDiffOn ℝ 2 f {z : ℂ | 0 < z.im})
    (hN : ∀ x : ℝ, fderivWithin ℝ f {z : ℂ | 0 ≤ z.im} x Complex.I = 0)
    (hL : _root_.MeasureTheory.LocallyIntegrable (Laplacian.laplacian f) (volume.restrict {z : ℂ | 0 < z.im})) :
    (∫ z : ℂ, Laplacian.laplacian φ z • evenReflection f z) =
      ∫ z : ℂ, φ z • evenReflection (Laplacian.laplacian f) z := by
  let ψ : ℂ → ℝ := fun z => φ z + φ (Complex.conjLIE z)
  have he : ContDiff ℝ 2 (Complex.conjLIE : ℂ → ℂ) := Complex.conjCLE.contDiff
  have hψ : ContDiff ℝ 2 ψ := hφ.add (hφ.comp he)
  have hcψ : HasCompactSupport ψ := hc.add (hc.comp_homeomorph Complex.conjLIE.toHomeomorph)
  have hψN (x : ℝ) : fderiv ℝ ψ x Complex.I = 0 := by
    have hd := (hφ.differentiable (by norm_num) (x : ℂ)).hasFDerivAt.add
      ((hφ.differentiable (by norm_num) (Complex.conjLIE x)).hasFDerivAt.comp (x : ℂ)
        Complex.conjCLE.hasFDerivAt)
    change fderiv ℝ (φ + φ ∘ Complex.conjLIE) x Complex.I = 0
    rw [hd.fderiv]
    simp
  have hψΔ (z : ℂ) : Laplacian.laplacian ψ z =
      Laplacian.laplacian φ z + Laplacian.laplacian φ (Complex.conjLIE z) := by
    change Laplacian.laplacian (φ + φ ∘ Complex.conjLIE) z = _
    rw [hφ.contDiffAt.laplacian_add (hφ.comp he).contDiffAt,
      Complex.conjLIE.laplacian_comp φ]
  have hU : MeasurableSet {z : ℂ | 0 < z.im} :=
    (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  have hfc : _root_.MeasureTheory.LocallyIntegrable f (volume.restrict {z : ℂ | 0 < z.im}) := by
    apply ((continuous_evenReflection hf.continuousOn).locallyIntegrable.mono_measure
      (Measure.restrict_le_self)).congr
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem hU] with z hz
    exact evenReflection_of_im_nonneg f (show 0 < z.im from hz).le
  have hΔφc : Continuous (Laplacian.laplacian φ) :=
    continuous_iff_continuousAt.mpr (fun _ => hφ.contDiffAt.continuousAt_laplacian)
  have hcΔ : HasCompactSupport (Laplacian.laplacian φ) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_laplacian_subset φ)
  rw [integral_smul_evenReflection
    (hfc.integrable_smul_left_of_hasCompactSupport hΔφc hcΔ)
    (hfc.integrable_smul_left_of_hasCompactSupport (hΔφc.comp Complex.conjLIE.continuous)
      (hcΔ.comp_homeomorph Complex.conjLIE.toHomeomorph)),
    integral_smul_evenReflection
    (hL.integrable_smul_left_of_hasCompactSupport hφ.continuous hc)
    (hL.integrable_smul_left_of_hasCompactSupport (hφ.continuous.comp Complex.conjLIE.continuous)
      (hc.comp_homeomorph Complex.conjLIE.toHomeomorph))]
  have hgreen := integral_smul_laplacian_sub_laplacian_smul_half_plane (a := 0)
    hψ hcψ hf hf2 (hL.integrable_smul_left_of_hasCompactSupport hψ.continuous hcψ)
  have hΔψc : Continuous (Laplacian.laplacian ψ) :=
    continuous_iff_continuousAt.mpr (fun _ => hψ.contDiffAt.continuousAt_laplacian)
  have hcΔψ : HasCompactSupport (Laplacian.laplacian ψ) :=
    hcψ.of_isClosed_subset (isClosed_tsupport _) (tsupport_laplacian_subset ψ)
  rw [_root_.MeasureTheory.integral_sub (hL.integrable_smul_left_of_hasCompactSupport hψ.continuous hcψ)
    (hfc.integrable_smul_left_of_hasCompactSupport hΔψc hcΔψ)] at hgreen
  have hh : (∫ z in {z : ℂ | 0 < z.im}, ψ z • Laplacian.laplacian f z) =
      ∫ z in {z : ℂ | 0 < z.im}, Laplacian.laplacian ψ z • f z := by
    apply sub_eq_zero.mp
    simpa [hN, hψN] using hgreen
  simpa only [hψΔ] using hh.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integral_laplacian_smul_evenReflection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integral_laplacian_smul_evenReflection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integral_laplacian_smul_evenReflection ``Submission.DifferentialGeometry.Analysis.integral_laplacian_smul_evenReflection

end DifferentialGeometry.Analysis
