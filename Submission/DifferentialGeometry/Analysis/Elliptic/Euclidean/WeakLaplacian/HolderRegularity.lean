import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Laplacian.Calculus
import Submission.DifferentialGeometry.Analysis.Integration.Integral.LaplacianTests
import Submission.DifferentialGeometry.Analysis.Schauder.Holder.Cutoff
import Submission.DifferentialGeometry.Analysis.Elliptic.Euclidean.WeakLaplacianRegularity
import Submission.DifferentialGeometry.Analysis.Schauder.Holder.IteratedDerivative
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Classical
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Divergence.Local

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter _root_.Metric
open scoped _root_.ENNReal _root_.NNReal _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean
open _root_.Submission.DifferentialGeometry.Analysis.Schauder

variable {d : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)

theorem exists_holder_iteratedFDeriv_two_of_holder_weak_laplacian_on_concentric_balls
    {Ω : Set V} (hΩ : IsOpen Ω) {u f : V → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u Ω) (hf : _root_.MeasureTheory.MemLp f 2 (volume.restrict Ω))
    (hdiv : DeGiorgi.HasWeakDiv f hu.weakGrad Ω)
    {G : V → V} (hG : G =ᵐ[volume.restrict Ω] hu.weakGrad)
    {c : V} {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hball : _root_.Metric.closedBall c R ⊆ Ω)
    {α Ku Kf : ℝ≥0} {KG : Fin d → ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    (huH : HolderOnWith Ku α u (_root_.Metric.closedBall c R))
    (hfH : HolderOnWith Kf α f (_root_.Metric.closedBall c R))
    (hGH : ∀ j, HolderOnWith (KG j) α (fun x => G x j) (_root_.Metric.closedBall c R)) :
    ∃ C : ℝ≥0, ContDiffOn ℝ 2 u (_root_.Metric.ball c r) ∧
      HolderOnWith C α (iteratedFDeriv ℝ 2 u) (_root_.Metric.ball c r) := by
  let β : ContDiffBump c := ⟨r, (r + R) / 2, hr, by linarith⟩
  have hβs : tsupport β ⊆ _root_.Metric.ball c R := by
    rw [β.tsupport_eq]
    exact _root_.Metric.closedBall_subset_ball (by dsimp only [β]; linarith)
  have hβΩ : tsupport β ⊆ Ω := hβs.trans (ball_subset_closedBall.trans hball)
  have hβ : ContDiff ℝ ∞ (β : V → ℝ) := β.contDiff
  let D (j : Fin d) (x : V) := fderiv ℝ β x (EuclideanSpace.single j 1)
  have hD (j : Fin d) : ContDiff ℝ ∞ (D j) :=
    (hβ.fderiv_right (by simp)).clm_apply contDiff_const
  have hDc (j : Fin d) : HasCompactSupport (D j) := β.hasCompactSupport.fderiv_apply ℝ _
  have hDs (j : Fin d) : tsupport (D j) ⊆ tsupport β := tsupport_fderiv_apply_subset ℝ _
  have hL : ContDiff ℝ ∞ (Laplacian.laplacian (β : V → ℝ)) := by
    have heq : Laplacian.laplacian (β : V → ℝ) = fun x => ∑ j : Fin d,
        fderiv ℝ (D j) x (EuclideanSpace.single j 1) := by
      funext x
      exact laplacian_eq_sum_euclidean_fderiv β.contDiff.contDiffAt
    rw [heq]
    exact ContDiff.sum fun j _ => ((hD j).fderiv_right (by simp)).clm_apply contDiff_const
  have hLc : HasCompactSupport (Laplacian.laplacian (β : V → ℝ)) :=
    β.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _) (tsupport_laplacian_subset _)
  have hLs : tsupport (Laplacian.laplacian (β : V → ℝ)) ⊆ tsupport β := tsupport_laplacian_subset _
  obtain ⟨Bf, Cf, hBf, hCf⟩ := exists_holderWith_smul_cutoff_of_holderOnWith
    (_root_.ProperSpace.isCompact_closedBall c R) hα hα1.le hfH β.contDiff β.hasCompactSupport
    (hβs.trans _root_.Metric.ball_subset_closedBall)
  obtain ⟨Bu, Cu, hBu, hCu⟩ := exists_holderWith_smul_cutoff_of_holderOnWith
    (_root_.ProperSpace.isCompact_closedBall c R) hα hα1.le huH
    (hL.of_le (by norm_cast)) hLc (hLs.trans (hβs.trans _root_.Metric.ball_subset_closedBall))
  choose BG CG hBG hCG using fun j => exists_holderWith_smul_cutoff_of_holderOnWith
    (_root_.ProperSpace.isCompact_closedBall c R) hα hα1.le (hGH j)
    ((hD j).of_le (by norm_cast)) (hDc j) ((hDs j).trans (hβs.trans _root_.Metric.ball_subset_closedBall))
  let q : V → ℝ := fun x => β x * f x + 2 * (∑ j, D j x * G x j) +
    Laplacian.laplacian (β : V → ℝ) x * u x
  let B : ℝ≥0 := Bf + 2 * ∑ j, BG j + Bu
  have hqH : HolderWith (Cf + (∑ j, CG j) * ‖(2 : ℝ)‖₊ + Cu) α q := by
    have hh := (hCf.add ((holderWith_finset_sum Finset.univ fun j _ => hCG j).smul (2 : ℝ))).add hCu
    exact holderWith_congr hh (fun x => by rfl)
  have hqB (x : V) : ‖q x‖ ≤ B := by
    have hsum : ‖∑ j, D j x * G x j‖ ≤ ∑ j, (BG j : ℝ) :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hBG j x)
    dsimp only [q, B]
    push_cast
    apply (norm_add_le _ _).trans
    apply add_le_add _ (hBu x)
    apply (norm_add_le _ _).trans
    apply add_le_add (hBf x)
    rw [norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left hsum (by norm_num)
  have hzero (x : V) (hx : x ∉ tsupport β) : β x = 0 ∧
      Laplacian.laplacian (β : V → ℝ) x = 0 ∧ ∀ j, D j x = 0 :=
    ⟨image_eq_zero_of_notMem_tsupport hx,
      image_eq_zero_of_notMem_tsupport (fun ht => hx (hLs ht)),
      fun j => image_eq_zero_of_notMem_tsupport (fun ht => hx (hDs j ht))⟩
  let u₁ : V → ℝ := fun x => β x * u x
  have hu₁ : Continuous u₁ := by
    have hh := β.continuous.continuousOn.mul
      ((huH.continuousOn hα).mono _root_.Metric.ball_subset_closedBall)
    exact hh.continuous_of_tsupport_subset _root_.Metric.isOpen_ball (tsupport_mul_subset_left.trans hβs)
  have hu₁c : HasCompactSupport u₁ := β.hasCompactSupport.mul_right
  have hw (φ : V → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
      (∫ x, Laplacian.laplacian φ x • u₁ x) = ∫ x, φ x • q x := by
    have hh := integral_laplacian_mul_cutoff_eq_of_hasWeakDiv hΩ hu hf hdiv
      β.contDiff β.hasCompactSupport hβΩ hφ hφc
    simp only [smul_eq_mul, u₁]
    apply hh.trans
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [(_root_.MeasureTheory.ae_restrict_iff' hΩ.measurableSet).mp hG] with x hx
    by_cases hxΩ : x ∈ Ω
    · simp only [q, D, hx hxΩ]
    · have hn : x ∉ tsupport β := fun ht => hxΩ (hβΩ ht)
      rcases hzero x hn with ⟨h1, h2, h3⟩
      simp only [q, h1, h2, h3, _root_.MulZeroClass.zero_mul, Finset.sum_const_zero, _root_.MulZeroClass.mul_zero, zero_add, D]
  have hw2 (φ : V → ℝ) (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
      (∫ x, Laplacian.laplacian φ x • u₁ x) = ∫ x, φ x • q x :=
    integral_laplacian_smul_eq_of_smooth_test hu₁.locallyIntegrable
      (hqH.continuous hα).locallyIntegrable hw hφ hφc
  obtain ⟨C, hu₂, hHess⟩ :=
    DifferentialGeometry.Analysis.exists_holder_iteratedFDeriv_two_of_holder_weak_laplacian
      hu₁ hu₁c hqB hw2 hα hα1 hqH
  have heq (x : V) (hx : x ∈ _root_.Metric.ball c r) : u₁ =ᶠ[𝓝 x] u := by
    filter_upwards [β.eventuallyEq_one_of_mem_ball hx] with y hy
    simp only [u₁, hy, Pi.one_apply, one_mul]
  refine ⟨C, hu₂.contDiffOn.congr (fun x hx => (heq x hx).self_of_nhds.symm), ?_⟩
  intro x hx y hy
  rw [← ((heq x hx).iteratedFDeriv (𝕜 := ℝ) 2).self_of_nhds,
    ← ((heq y hy).iteratedFDeriv (𝕜 := ℝ) 2).self_of_nhds]
  exact hHess x y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_holder_iteratedFDeriv_two_of_holder_weak_laplacian_on_concentric_balls then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_holder_iteratedFDeriv_two_of_holder_weak_laplacian_on_concentric_balls"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_holder_iteratedFDeriv_two_of_holder_weak_laplacian_on_concentric_balls ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_holder_iteratedFDeriv_two_of_holder_weak_laplacian_on_concentric_balls

theorem exists_holder_iteratedFDeriv_two_of_holder_weak_laplacian_on_ball
    {Ω : Set V} (hΩ : IsOpen Ω) {u f : V → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u Ω) (hf : _root_.MeasureTheory.MemLp f 2 (volume.restrict Ω))
    (hdiv : DeGiorgi.HasWeakDiv f hu.weakGrad Ω)
    {G : V → V} (hG : G =ᵐ[volume.restrict Ω] hu.weakGrad)
    {c : V} {R : ℝ} (hR : 0 < R) (hball : _root_.Metric.closedBall c R ⊆ Ω)
    {α Ku Kf : ℝ≥0} {KG : Fin d → ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    (huH : HolderOnWith Ku α u (_root_.Metric.closedBall c R))
    (hfH : HolderOnWith Kf α f (_root_.Metric.closedBall c R))
    (hGH : ∀ j, HolderOnWith (KG j) α (fun x => G x j) (_root_.Metric.closedBall c R)) :
    ∃ C : ℝ≥0, ContDiffOn ℝ 2 u (_root_.Metric.ball c (R / 2)) ∧
      HolderOnWith C α (iteratedFDeriv ℝ 2 u) (_root_.Metric.ball c (R / 2)) := by
  exact exists_holder_iteratedFDeriv_two_of_holder_weak_laplacian_on_concentric_balls
      hΩ hu hf hdiv hG (half_pos hR) (half_lt_self hR) hball hα hα1 huH hfH hGH

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_holder_iteratedFDeriv_two_of_holder_weak_laplacian_on_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_holder_iteratedFDeriv_two_of_holder_weak_laplacian_on_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_holder_iteratedFDeriv_two_of_holder_weak_laplacian_on_ball ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_holder_iteratedFDeriv_two_of_holder_weak_laplacian_on_ball

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

noncomputable section
open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Metric
open scoped _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean
open _root_.Submission.DifferentialGeometry.Analysis.Schauder

variable {d : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)

theorem contDiffOn_iteratedFDeriv_apply
    {Ω : Set V} (hΩ : IsOpen Ω) {u : V → ℝ} {n m : ℕ}
    (hu : ContDiffOn ℝ (n + m : ℕ) u Ω) (v : Fin n → V) :
    ContDiffOn ℝ m (fun x => iteratedFDeriv ℝ n u x v) Ω := by
  let L := ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => V) ℝ v
  intro x hx
  exact (L.contDiff.contDiffAt.comp x
    ((hu.contDiffAt (hΩ.mem_nhds hx)).iteratedFDeriv_right (by norm_cast; omega))).contDiffWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.contDiffOn_iteratedFDeriv_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.contDiffOn_iteratedFDeriv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.contDiffOn_iteratedFDeriv_apply ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.contDiffOn_iteratedFDeriv_apply

theorem exists_holder_iteratedFDeriv_add_two_of_weak_laplacian
    {Ω : Set V} (hΩ : IsOpen Ω) {u f : V → ℝ} {n : ℕ}
    (hu : ContDiffOn ℝ (n + 1 : ℕ) u Ω) (hf : ContDiffOn ℝ n f Ω)
    (hdiv : DeGiorgi.HasWeakDiv f (DeGiorgi.smoothGradField u) Ω)
    {c : V} {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hball : _root_.Metric.closedBall c R ⊆ Ω)
    {α Ku Kf : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    (huH : HolderOnWith Ku α (iteratedFDeriv ℝ (n + 1) u) (_root_.Metric.closedBall c R))
    (hfH : HolderOnWith Kf α (iteratedFDeriv ℝ n f) (_root_.Metric.closedBall c R)) :
    ∃ C : ℝ≥0, ContDiffOn ℝ (n + 2 : ℕ) u (_root_.Metric.ball c r) ∧
      HolderOnWith C α (iteratedFDeriv ℝ (n + 2) u) (_root_.Metric.ball c r) := by
  let s := (r + R) / 2
  have hrs : r < s := by dsimp only [s]; linarith
  have hsR : s < R := by dsimp only [s]; linarith
  have hsmall : _root_.Metric.closedBall c s ⊆ _root_.Metric.ball c R := _root_.Metric.closedBall_subset_ball hsR
  have hsmallR : _root_.Metric.closedBall c s ⊆ _root_.Metric.closedBall c R := hsmall.trans _root_.Metric.ball_subset_closedBall
  have hBΩ : _root_.Metric.ball c R ⊆ Ω := ball_subset_closedBall.trans hball
  have hresult (v : Fin n → Fin d) : ∃ K : ℝ≥0,
      ContDiffOn ℝ 2 (fun x => iteratedFDeriv ℝ n u x
        (fun i => EuclideanSpace.single (v i) 1)) (_root_.Metric.ball c r) ∧
      HolderOnWith K α (iteratedFDeriv ℝ 2 (fun x => iteratedFDeriv ℝ n u x
        (fun i => EuclideanSpace.single (v i) 1))) (_root_.Metric.ball c r) := by
    let w (x : V) := iteratedFDeriv ℝ n u x (fun i => EuclideanSpace.single (v i) 1)
    let g (x : V) := iteratedFDeriv ℝ n f x (fun i => EuclideanSpace.single (v i) 1)
    have hw1 : ContDiffOn ℝ 1 w Ω := contDiffOn_iteratedFDeriv_apply hΩ hu _
    have hg0 : ContDiffOn ℝ 0 g Ω :=
      contDiffOn_iteratedFDeriv_apply hΩ (by simpa only [Nat.add_zero] using hf) _
    obtain ⟨hw, hDw⟩ := exists_memW1pWitness_of_contDiffOn_closedBall hΩ hw1 hball 2
    let G := DeGiorgi.smoothGradField w
    have hGeq : G = (hw.weakGrad) := by
      funext x
      ext j
      exact (hDw x j).symm
    let : _root_.MeasureTheory.IsFiniteMeasure (volume.restrict (_root_.Metric.ball c R)) :=
      isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
    have hgLp : _root_.MeasureTheory.MemLp g 2 (volume.restrict (_root_.Metric.ball c R)) := by
      have hc := hg0.continuousOn.mono hball
      obtain ⟨B, hB⟩ := (_root_.ProperSpace.isCompact_closedBall c R).exists_bound_of_continuousOn hc
      apply MemLp.of_bound ((hc.mono _root_.Metric.ball_subset_closedBall).aestronglyMeasurable
        isOpen_ball.measurableSet) B
      filter_upwards [_root_.MeasureTheory.ae_restrict_mem isOpen_ball.measurableSet] with x hx
      exact hB x (_root_.Metric.ball_subset_closedBall hx)
    have hdivw : DeGiorgi.HasWeakDiv g hw.weakGrad (_root_.Metric.ball c R) := by
      have hh := (hasWeakDiv_iteratedFDeriv_apply_of_contDiffOn hΩ hu hf hdiv v).restrict hBΩ
      exact hh.congr_ae EventuallyEq.rfl (Eventually.of_forall fun x => congrFun hGeq x)
    obtain ⟨Kw, hKw⟩ := exists_holderWith_restrict_of_contDiffOn_isCompact
      (_root_.ProperSpace.isCompact_closedBall c s) (convex_closedBall _ _) (hw1.mono (hsmallR.trans hball)) hα1.le
    obtain ⟨Kg, hKg⟩ := exists_holderOnWith_clm_comp (hfH.mono hsmallR)
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => V) ℝ
        (fun i => EuclideanSpace.single (v i) 1))
    have hGholder (j : Fin d) : ∃ K : ℝ≥0,
        HolderOnWith K α (fun x => G x j) (_root_.Metric.closedBall c s) := by
      let t : Fin (n + 1) → V := Fin.cons (EuclideanSpace.single j 1)
        (fun i => EuclideanSpace.single (v i) 1)
      obtain ⟨K, hK⟩ := exists_holderOnWith_clm_comp (huH.mono hsmallR)
        (ContinuousMultilinearMap.apply ℝ (fun _ : Fin (n + 1) => V) ℝ t)
      have heq (x : V) (hx : x ∈ _root_.Metric.closedBall c s) : G x j = iteratedFDeriv ℝ (n + 1) u x t := by
        have hxΩ := hball (hsmallR hx)
        have hd := (hu.contDiffAt (hΩ.mem_nhds hxΩ)).differentiableAt_iteratedFDeriv
          (m := n) (by norm_cast; omega)
        change fderiv ℝ w x (EuclideanSpace.single j 1) = _
        exact (hd.iteratedFDeriv_succ_apply_left' (m := t)).symm
      refine ⟨K, ?_⟩
      intro x hx y hy
      change _root_.EDist.edist (G x j) (G y j) ≤ _
      rw [heq x hx, heq y hy]
      exact hK x hx y hy
    choose KG hKG using hGholder
    exact exists_holder_iteratedFDeriv_two_of_holder_weak_laplacian_on_concentric_balls
      _root_.Metric.isOpen_ball hw hgLp hdivw (Eventually.of_forall fun x => congrFun hGeq x)
      hr hrs hsmall hα hα1 (HolderWith.restrict_iff.mp hKw) hKg hKG
  choose K hK hKH using hresult
  have hJ : ContDiffOn ℝ 2 (iteratedFDeriv ℝ n u) (_root_.Metric.ball c r) := by
    apply contDiffOn_continuousMultilinearMap_of_basis (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
    intro v
    simpa only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply] using hK v
  have hu2 : ContDiffOn ℝ (n + 2 : ℕ) u (_root_.Metric.ball c r) :=
    contDiffOn_add_two_of_contDiffOn_iteratedFDeriv _root_.Metric.isOpen_ball
      ((hu.of_le (by norm_cast; omega)).mono ((_root_.Metric.ball_subset_ball hrR.le).trans hBΩ)) hJ
  obtain ⟨C, hC⟩ := exists_holderOnWith_iteratedFDeriv_add_two_of_basis
    (EuclideanSpace.basisFun (Fin d) ℝ).toBasis _root_.Metric.isOpen_ball hu2 (by
      intro v
      refine ⟨K v, ?_⟩
      simpa only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply] using hKH v)
  exact ⟨C, hu2, hC⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_holder_iteratedFDeriv_add_two_of_weak_laplacian then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_holder_iteratedFDeriv_add_two_of_weak_laplacian"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_holder_iteratedFDeriv_add_two_of_weak_laplacian ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_holder_iteratedFDeriv_add_two_of_weak_laplacian

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end
