import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Divergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.ENNReal _root_.ContDiff _root_.Topology

namespace DeGiorgi

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem HasWeakDiv.mul_cutoff_univ
    {Ω : Set E} {f η : E → ℝ} {G : E → E}
    (hG : ∀ j, _root_.MeasureTheory.LocallyIntegrable (fun x => G x j) (volume.restrict Ω))
    (hf : _root_.MeasureTheory.LocallyIntegrable f (volume.restrict Ω)) (hdiv : HasWeakDiv f G Ω)
    (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η) (hηs : tsupport η ⊆ Ω) :
    HasWeakDiv (fun x => η x * f x + ∑ j, fderiv ℝ η x (EuclideanSpace.single j 1) * G x j)
      (fun x => η x • G x) univ := by
  let D (j : Fin d) (x : E) := fderiv ℝ η x (EuclideanSpace.single j 1)
  have hDc (j : Fin d) : Continuous (D j) :=
    (hη.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDcs (j : Fin d) : HasCompactSupport (D j) := hηc.fderiv_apply ℝ _
  have hDs (j : Fin d) : tsupport (D j) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ _).trans hηs
  intro φ hφ hφc _
  have hm := hdiv (fun x => η x * φ x) (hη.mul hφ) hηc.mul_right
    ((tsupport_smul_subset_left η φ).trans hηs)
  have hfd (x : E) (j : Fin d) :
      fderiv ℝ (fun y => η y * φ y) x (EuclideanSpace.single j 1) =
        η x * fderiv ℝ φ x (EuclideanSpace.single j 1) + D j x * φ x := by
    rw [fderiv_fun_mul (hη.differentiable (by simp)).differentiableAt
      (hφ.differentiable (by simp)).differentiableAt]
    simp only [add_apply, smul_apply, smul_eq_mul, D]
    ring
  have hprod {a b : E → ℝ} (hb : _root_.MeasureTheory.LocallyIntegrable b (volume.restrict Ω))
      (ha : Continuous a) (hac : HasCompactSupport a) (has : tsupport a ⊆ Ω) :
      Integrable (fun x => b x * a x) volume := by
    have hi : _root_.MeasureTheory.IntegrableOn (fun x => b x * a x) Ω :=
      hb.integrable_smul_right_of_hasCompactSupport ha hac
    apply (_root_.MeasureTheory.integrableOn_iff_integrable_of_support_subset _).mp hi
    intro x hx
    by_contra hxΩ
    exact hx (by
      change b x * a x = 0
      rw [image_eq_zero_of_notMem_tsupport (fun ht => hxΩ (has ht)), _root_.MulZeroClass.mul_zero])
  have hI₁ (j : Fin d) : _root_.MeasureTheory.Integrable (fun x => η x * G x j *
      fderiv ℝ φ x (EuclideanSpace.single j 1)) volume := by
    have hh := hprod (a := fun x => η x * fderiv ℝ φ x (EuclideanSpace.single j 1))
      (hG j) (hη.continuous.mul ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const))
      hηc.mul_right (tsupport_mul_subset_left.trans hηs)
    exact hh.congr (Eventually.of_forall fun x => by dsimp only; ring)
  have hI₂ (j : Fin d) : _root_.MeasureTheory.Integrable (fun x => D j x * G x j * φ x) volume := by
    have hh := hprod (hG j) ((hDc j).mul hφ.continuous) (hDcs j).mul_right
      (tsupport_mul_subset_left.trans (hDs j))
    exact hh.congr (Eventually.of_forall fun x => by simp only [Pi.mul_apply]; ring)
  have hI₃ : _root_.MeasureTheory.Integrable (fun x => η x * f x * φ x) volume := by
    have hh := hprod hf (hη.continuous.mul hφ.continuous) hηc.mul_right
      (tsupport_mul_subset_left.trans hηs)
    exact hh.congr (Eventually.of_forall fun x => by simp only [Pi.mul_apply]; ring)
  have hzero (x : E) (hx : x ∉ Ω) : η x = 0 ∧ ∀ j, D j x = 0 :=
    ⟨image_eq_zero_of_notMem_tsupport (fun h => hx (hηs h)),
      fun j => image_eq_zero_of_notMem_tsupport (fun h => hx (hDs j h))⟩
  have hleft : (∫ x in Ω, ∑ j, G x j *
      fderiv ℝ (fun y => η y * φ y) x (EuclideanSpace.single j 1)) =
      (∫ x, ∑ j, η x * G x j * fderiv ℝ φ x (EuclideanSpace.single j 1)) +
        ∫ x, ∑ j, D j x * G x j * φ x := by
    calc
      _ = ∫ x in Ω, ((∑ j, η x * G x j * fderiv ℝ φ x (EuclideanSpace.single j 1)) +
          ∑ j, D j x * G x j * φ x) := by
        apply _root_.MeasureTheory.integral_congr_ae
        filter_upwards with x
        simp only [hfd, mul_add, Finset.sum_add_distrib]
        congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring
      _ = ∫ x, ((∑ j, η x * G x j * fderiv ℝ φ x (EuclideanSpace.single j 1)) +
          ∑ j, D j x * G x j * φ x) :=
        _root_.MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
          simp only [(hzero x hx).1, (hzero x hx).2, _root_.MulZeroClass.zero_mul, Finset.sum_const_zero, zero_add]
      _ = _ := _root_.MeasureTheory.integral_add (_root_.MeasureTheory.integrable_finsetSum _ fun j _ => hI₁ j)
        (_root_.MeasureTheory.integrable_finsetSum _ fun j _ => hI₂ j)
  have hright : (∫ x in Ω, f x * (η x * φ x)) = ∫ x, η x * f x * φ x := by
    rw [_root_.MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact _root_.MeasureTheory.integral_congr_ae (Eventually.of_forall fun x => by ring)
    · intro x hx
      rw [(hzero x hx).1]
      ring
  rw [hleft, hright] at hm
  simp only [Measure.restrict_univ, PiLp.smul_apply, smul_eq_mul]
  change (∫ x, ∑ j, η x * G x j * fderiv ℝ φ x (EuclideanSpace.single j 1)) =
    -∫ x, (η x * f x + ∑ j, D j x * G x j) * φ x
  simp_rw [add_mul, Finset.sum_mul]
  rw [_root_.MeasureTheory.integral_add hI₃ (_root_.MeasureTheory.integrable_finsetSum _ fun j _ => hI₂ j)]
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.HasWeakDiv.mul_cutoff_univ then
    throwError "Refusing to shadow existing declaration DeGiorgi.HasWeakDiv.mul_cutoff_univ"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.HasWeakDiv.mul_cutoff_univ ``Submission.DeGiorgi.HasWeakDiv.mul_cutoff_univ

theorem hasWeakDiv_of_hasWeakPartialDeriv
    {Ω : Set E} {F H : E → E}
    (hF : ∀ j, _root_.MeasureTheory.LocallyIntegrable (fun x => F x j) (volume.restrict Ω))
    (hH : ∀ j, _root_.MeasureTheory.LocallyIntegrable (fun x => H x j) (volume.restrict Ω))
    (hpartial : ∀ j, HasWeakPartialDeriv j (fun x => H x j) (fun x => F x j) Ω) :
    HasWeakDiv (fun x => ∑ j, H x j) F Ω := by
  intro φ hφ hφc hφs
  have hleft (j : Fin d) : _root_.MeasureTheory.IntegrableOn
      (fun x => F x j * fderiv ℝ φ x (EuclideanSpace.single j 1)) Ω :=
    (hF j).integrable_smul_right_of_hasCompactSupport
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const) (hφc.fderiv_apply ℝ _)
  have hright (j : Fin d) : _root_.MeasureTheory.IntegrableOn (fun x => H x j * φ x) Ω :=
    (hH j).integrable_smul_right_of_hasCompactSupport hφ.continuous hφc
  rw [_root_.MeasureTheory.integral_finsetSum _ (fun j _ => hleft j)]
  simp_rw [hpartial _ φ hφ hφc hφs, Finset.sum_neg_distrib, Finset.sum_mul]
  rw [_root_.MeasureTheory.integral_finsetSum _ (fun j _ => hright j)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.hasWeakDiv_of_hasWeakPartialDeriv then
    throwError "Refusing to shadow existing declaration DeGiorgi.hasWeakDiv_of_hasWeakPartialDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.hasWeakDiv_of_hasWeakPartialDeriv ``Submission.DeGiorgi.hasWeakDiv_of_hasWeakPartialDeriv

end DeGiorgi

end

noncomputable section
open _root_.MeasureTheory _root_.Set _root_.Filter

namespace DeGiorgi

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem HasWeakDiv.restrict
    {Ω U : Set E} (hU : U ⊆ Ω) {f : E → ℝ} {G : E → E}
    (h : HasWeakDiv f G Ω) : HasWeakDiv f G U := by
  intro φ hφ hφc hφs
  have hh := h φ hφ hφc (hφs.trans hU)
  have hleft (S : Set E) (hUS : U ⊆ S) :
      (∫ x in S, ∑ j, G x j * fderiv ℝ φ x (EuclideanSpace.single j 1)) =
        ∫ x, ∑ j, G x j * fderiv ℝ φ x (EuclideanSpace.single j 1) := by
    apply _root_.MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hn : x ∉ tsupport φ := fun ht => hx (hUS (hφs ht))
    simp only [fderiv_of_notMem_tsupport ℝ hn, zero_apply,
      _root_.MulZeroClass.mul_zero, Finset.sum_const_zero]
  have hright (S : Set E) (hUS : U ⊆ S) :
      (∫ x in S, f x * φ x) = ∫ x, f x * φ x := by
    apply _root_.MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hUS (hφs ht))), _root_.MulZeroClass.mul_zero]
  rw [hleft Ω hU, hright Ω hU] at hh
  rw [hleft U Subset.rfl, hright U Subset.rfl]
  exact hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.HasWeakDiv.restrict then
    throwError "Refusing to shadow existing declaration DeGiorgi.HasWeakDiv.restrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.HasWeakDiv.restrict ``Submission.DeGiorgi.HasWeakDiv.restrict

end DeGiorgi

end

noncomputable section
open _root_.MeasureTheory _root_.Set _root_.Filter

namespace DeGiorgi

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem integrable_mul_partial
    {Ω : Set E} {f φ : E → ℝ} (hf : _root_.MeasureTheory.LocallyIntegrableOn f Ω _root_.MeasureTheory.MeasureSpace.volume)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω)
    (j : Fin d) : _root_.MeasureTheory.IntegrableOn
      (fun x => f x * fderiv ℝ φ x (EuclideanSpace.single j 1)) Ω := by
  let D := fun x => fderiv ℝ φ x (EuclideanSpace.single j 1)
  have hDc : HasCompactSupport D := hc.fderiv_apply ℝ _
  have hDs : tsupport D ⊆ Ω := (tsupport_fderiv_apply_subset ℝ _).trans hs
  have hD : Continuous D := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hi : _root_.MeasureTheory.IntegrableOn (fun x => f x * D x) (tsupport D) :=
    (hf.integrableOn_compact_subset hDs hDc).mul_continuousOn hD.continuousOn hDc
  have hg : _root_.MeasureTheory.Integrable (fun x => f x * D x) volume :=
    (_root_.MeasureTheory.integrableOn_iff_integrable_of_support_subset
      ((Function.support_mul_subset_right f D).trans (subset_tsupport D))).mp hi
  exact hg.restrict

run_cmd do
  let target := ``Submission.DeGiorgi.integrable_mul_partial
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DeGiorgi.integrable_mul_partial target :: scope.openDecls } }

theorem HasWeakDiv.comm_of_locallyIntegrableOn
    {Omega : Set E} {f g : E → ℝ} {F G : E → E} {l : Fin d}
    (hdiv : HasWeakDiv f F Omega)
    (hpartial : HasWeakPartialDeriv l g f Omega)
    (hparts : ∀ i : Fin d,
      HasWeakPartialDeriv l (fun x => G x i) (fun x => F x i) Omega)
    (hF : ∀ i : Fin d, _root_.MeasureTheory.LocallyIntegrableOn (fun x => F x i) Omega _root_.MeasureTheory.MeasureSpace.volume)
    (hG : ∀ i : Fin d, _root_.MeasureTheory.LocallyIntegrableOn (fun x => G x i) Omega _root_.MeasureTheory.MeasureSpace.volume) :
    HasWeakDiv g G Omega := by
  intro phi hphi hphi_cpt hphi_sub
  let D : Fin d → E → ℝ := fun i x => (fderiv ℝ phi x) (EuclideanSpace.single i 1)
  have hdphi : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ phi) := hphi.fderiv_right (by simp)
  have hD : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (D i) :=
    fun i => hdphi.clm_apply contDiff_const
  have hD_cpt : ∀ i, HasCompactSupport (D i) :=
    fun i => hphi_cpt.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
  have hD_sub : ∀ i, tsupport (D i) ⊆ Omega := fun i =>
    (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans hphi_sub
  have hcomm : ∀ (x : E) (i : Fin d),
      (fderiv ℝ (D i) x) (EuclideanSpace.single l 1) =
        (fderiv ℝ (D l) x) (EuclideanSpace.single i 1) := by
    intro x i
    simp only [D, fderiv_clm_apply (hdphi.differentiable (by simp) x)
      (differentiableAt_const _), fderiv_const_apply, add_apply,
      ContinuousLinearMap.comp_apply, zero_apply, map_zero, zero_add,
      ContinuousLinearMap.flip_apply]
    exact hphi.contDiffAt.isSymmSndFDerivAt (by
      rw [minSmoothness_of_isRCLikeNormedField]
      decide) (EuclideanSpace.single l 1) (EuclideanSpace.single i 1)
  have hparts_int : ∀ i : Fin d,
      (∫ x in Omega, G x i * D i x) =
        -(∫ x in Omega, F x i * (fderiv ℝ (D l) x) (EuclideanSpace.single i 1)) := by
    intro i
    have hi := hparts i (D i) (hD i) (hD_cpt i) (hD_sub i)
    have heq : (∫ x in Omega, F x i * (fderiv ℝ (D i) x) (EuclideanSpace.single l 1)) =
        ∫ x in Omega, F x i * (fderiv ℝ (D l) x) (EuclideanSpace.single i 1) :=
      _root_.MeasureTheory.integral_congr_ae (Eventually.of_forall fun x => by dsimp only; rw [hcomm x i])
    linarith
  have hG_int : ∀ i : Fin d, _root_.MeasureTheory.Integrable (fun x => G x i * D i x)
      (volume.restrict Omega) := fun i => integrable_mul_partial (hG i) hphi hphi_cpt hphi_sub i
  have hF_int : ∀ i : Fin d,
      _root_.MeasureTheory.Integrable (fun x => F x i * (fderiv ℝ (D l) x) (EuclideanSpace.single i 1))
        (volume.restrict Omega) :=
    fun i => integrable_mul_partial (hF i) (hD l) (hD_cpt l) (hD_sub l) i
  change (∫ x in Omega, ∑ i : Fin d, G x i * D i x) = _
  rw [_root_.MeasureTheory.integral_finsetSum _ (fun i _ => hG_int i)]
  simp_rw [hparts_int, Finset.sum_neg_distrib]
  rw [← _root_.MeasureTheory.integral_finsetSum _ (fun i _ => hF_int i),
    hdiv (D l) (hD l) (hD_cpt l) (hD_sub l), neg_neg]
  exact hpartial phi hphi hphi_cpt hphi_sub

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.HasWeakDiv.comm_of_locallyIntegrableOn then
    throwError "Refusing to shadow existing declaration DeGiorgi.HasWeakDiv.comm_of_locallyIntegrableOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.HasWeakDiv.comm_of_locallyIntegrableOn ``Submission.DeGiorgi.HasWeakDiv.comm_of_locallyIntegrableOn

end DeGiorgi

end
