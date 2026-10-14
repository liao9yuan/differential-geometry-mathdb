import Submission.DifferentialGeometry.Analysis.Sobolev.Tools.DifferenceQuotient
import Submission.DifferentialGeometry.External.DeGiorgi.SobolevSpace.WeakDerivatives
import Submission.DifferentialGeometry.External.DeGiorgi.EllipticCoefficients

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.MeasureTheory _root_.Metric _root_.Filter _root_.Topology _root_.Set _root_.Function
open scoped _root_.ENNReal _root_.NNReal _root_.Convolution _root_.Pointwise _root_.BigOperators _root_.InnerProductSpace

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
theorem diffQuot_bound_of_smooth_compactSupport
    {f : E → ℝ} (hf : ContDiff ℝ 1 f) (hf_support : HasCompactSupport f)
    (i : Fin d) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ h : ℝ, ∀ x : E,
        |DifferentialGeometry.Analysis.Sobolev.diffQuot i h f x| ≤ L := by
  obtain ⟨L, hL_nn, hLip⟩ :=
    DifferentialGeometry.Analysis.Sobolev.lipschitz_of_contDiff_compactSupport
      (d := d) hf hf_support
  refine ⟨L, hL_nn, fun h x => ?_⟩
  by_cases hh : h = 0
  · simp [DifferentialGeometry.Analysis.Sobolev.diffQuot, hh, hL_nn]
  · rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne (d := d) i hh f x]
    have hLip_apply :
        ‖f (x + h • EuclideanSpace.single i 1) - f x‖ ≤
          L * ‖x + h • EuclideanSpace.single i 1 - x‖ := hLip _ _
    have hsimp : x + h • EuclideanSpace.single i 1 - x =
        h • EuclideanSpace.single i 1 := by
      rw [add_sub_cancel_left]
    rw [hsimp] at hLip_apply
    have hsing_norm :
        ‖(EuclideanSpace.single i (1 : ℝ) : E)‖ = 1 := by simp
    have hnorm_smul :
        ‖h • EuclideanSpace.single i (1 : ℝ)‖ = |h| := by
      rw [norm_smul, hsing_norm, mul_one, Real.norm_eq_abs]
    rw [hnorm_smul] at hLip_apply
    rw [abs_div]
    have habs_h : 0 < |h| := abs_pos.mpr hh
    rw [div_le_iff₀ habs_h]
    have h_lhs_norm :
        |f (x + h • EuclideanSpace.single i 1) - f x| =
          ‖f (x + h • EuclideanSpace.single i 1) - f x‖ :=
      (Real.norm_eq_abs _).symm
    rw [h_lhs_norm]
    exact hLip_apply

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.diffQuot_bound_of_smooth_compactSupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.diffQuot_bound_of_smooth_compactSupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.diffQuot_bound_of_smooth_compactSupport ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.diffQuot_bound_of_smooth_compactSupport

structure SmoothEllipticBilinearForm
    (d : ℕ) [NeZero d] (Ω : Set (EuclideanSpace ℝ (Fin d))) where
  a : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ
  c : EuclideanSpace ℝ (Fin d) → ℝ
  symm : ∀ x i j, a x i j = a x j i
  smooth_a : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x : EuclideanSpace ℝ (Fin d) => a x i j)
  smooth_c : ContDiff ℝ (⊤ : ℕ∞) c
  lam : ℝ
  capLam : ℝ
  ellipticity_pos : 0 < lam
  ellipticity_le_upper : lam ≤ capLam
  coercive : ∀ x ∈ Ω, ∀ ξ : EuclideanSpace ℝ (Fin d),
    lam * ‖ξ‖ ^ 2 ≤ ⟪ξ, DeGiorgi.matMulE (a x) ξ⟫_ℝ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm

namespace SmoothEllipticBilinearForm

theorem contDiff_a {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω) (i j : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : E => B.a x i j) :=
  B.smooth_a i j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.contDiff_a then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.contDiff_a"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.contDiff_a ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.contDiff_a

theorem continuous_a {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω) (i j : Fin d) :
    Continuous (fun x : E => B.a x i j) :=
  (B.smooth_a i j).continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.continuous_a then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.continuous_a"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.continuous_a ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.continuous_a

theorem continuous_c {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω) :
    Continuous B.c :=
  B.smooth_c.continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.continuous_c then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.continuous_c"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.continuous_c ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.continuous_c

theorem lam_nonneg {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω) :
    0 ≤ B.lam := B.ellipticity_pos.le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.lam_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.lam_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.lam_nonneg ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.lam_nonneg

theorem capLam_pos {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω) :
    0 < B.capLam := lt_of_lt_of_le B.ellipticity_pos B.ellipticity_le_upper

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.capLam_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.capLam_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.capLam_pos ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.capLam_pos

theorem capLam_nonneg {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω) :
    0 ≤ B.capLam := B.capLam_pos.le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.capLam_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.capLam_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.capLam_nonneg ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.capLam_nonneg

theorem bounded_a_on_compact {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {K : Set E} (hK : IsCompact K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i j : Fin d, ∀ x ∈ K, |B.a x i j| ≤ M := by
  classical
  have h_each : ∀ ij : Fin d × Fin d, ∃ Mij : ℝ, 0 ≤ Mij ∧
      ∀ x ∈ K, |B.a x ij.1 ij.2| ≤ Mij := by
    intro ij
    rcases hK.bddAbove_image (B.continuous_a ij.1 ij.2 |>.abs.continuousOn) with ⟨Mij, hMij⟩
    refine ⟨max Mij 0, le_max_right _ _, fun x hx => ?_⟩
    have h := hMij (_root_.Set.mem_image_of_mem _ hx)
    exact h.trans (le_max_left _ _)
  let pairBound : Fin d × Fin d → ℝ := fun ij => Classical.choose (h_each ij)
  have pairBound_nn : ∀ ij, 0 ≤ pairBound ij := fun ij => (Classical.choose_spec (h_each ij)).1
  have pairBound_le : ∀ ij : Fin d × Fin d, ∀ x ∈ K,
      |B.a x ij.1 ij.2| ≤ pairBound ij := fun ij => (Classical.choose_spec (h_each ij)).2
  let M : ℝ := ∑ ij : Fin d × Fin d, pairBound ij
  have hM_nn : 0 ≤ M := Finset.sum_nonneg (fun ij _ => pairBound_nn ij)
  refine ⟨M, hM_nn, fun i j x hx => ?_⟩
  have hsingle : pairBound (i, j) ≤ M := by
    refine Finset.single_le_sum (f := pairBound) (s := Finset.univ) ?_ (Finset.mem_univ (i, j))
    intro ij _
    exact pairBound_nn ij
  exact (pairBound_le (i, j) x hx).trans hsingle

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.bounded_a_on_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.bounded_a_on_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.bounded_a_on_compact ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.bounded_a_on_compact

theorem bounded_c_on_compact {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {K : Set E} (hK : IsCompact K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ K, |B.c x| ≤ M := by
  rcases hK.bddAbove_image (B.continuous_c.abs.continuousOn) with ⟨M, hM⟩
  refine ⟨max M 0, le_max_right _ _, fun x hx => ?_⟩
  have h := hM (_root_.Set.mem_image_of_mem _ hx)
  exact h.trans (le_max_left _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.bounded_c_on_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.bounded_c_on_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.bounded_c_on_compact ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.bounded_c_on_compact

theorem bounded_fderiv_a_on_compact {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (k : Fin d) {K : Set E} (hK : IsCompact K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i j : Fin d, ∀ x ∈ K,
      |(fderiv ℝ (fun x : E => B.a x i j) x) (EuclideanSpace.single k 1)| ≤ M := by
  classical
  have h_each : ∀ ij : Fin d × Fin d, ∃ Mij : ℝ, 0 ≤ Mij ∧
      ∀ x ∈ K, |(fderiv ℝ (fun y : E => B.a y ij.1 ij.2) x)
        (EuclideanSpace.single k 1)| ≤ Mij := by
    intro ij
    have hcont : Continuous
        (fun x : E => (fderiv ℝ (fun y : E => B.a y ij.1 ij.2) x)
          (EuclideanSpace.single k 1)) :=
      ((B.contDiff_a ij.1 ij.2).continuous_fderiv (by simp)).clm_apply continuous_const
    rcases hK.bddAbove_image hcont.abs.continuousOn with ⟨Mij, hMij⟩
    refine ⟨max Mij 0, le_max_right _ _, fun x hx => ?_⟩
    have h := hMij (_root_.Set.mem_image_of_mem _ hx)
    exact h.trans (le_max_left _ _)
  let pairBound : Fin d × Fin d → ℝ := fun ij => Classical.choose (h_each ij)
  have pairBound_nn : ∀ ij, 0 ≤ pairBound ij := fun ij => (Classical.choose_spec (h_each ij)).1
  have pairBound_le : ∀ ij : Fin d × Fin d, ∀ x ∈ K,
      |(fderiv ℝ (fun y : E => B.a y ij.1 ij.2) x) (EuclideanSpace.single k 1)| ≤
        pairBound ij :=
    fun ij => (Classical.choose_spec (h_each ij)).2
  let M : ℝ := ∑ ij : Fin d × Fin d, pairBound ij
  have hM_nn : 0 ≤ M := Finset.sum_nonneg (fun ij _ => pairBound_nn ij)
  refine ⟨M, hM_nn, fun i j x hx => ?_⟩
  have hsingle : pairBound (i, j) ≤ M := by
    refine Finset.single_le_sum (f := pairBound) (s := Finset.univ) ?_ (Finset.mem_univ (i, j))
    intro ij _
    exact pairBound_nn ij
  exact (pairBound_le (i, j) x hx).trans hsingle

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.bounded_fderiv_a_on_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.bounded_fderiv_a_on_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.bounded_fderiv_a_on_compact ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.bounded_fderiv_a_on_compact

def principalIntegrand {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (u v : E → ℝ) (x : E) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d,
    B.a x i j *
      ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
      ((fderiv ℝ v x) (EuclideanSpace.single j 1))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.principalIntegrand then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.principalIntegrand"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.principalIntegrand ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.principalIntegrand

def bilin {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω) (u v : E → ℝ) : ℝ :=
  ∫ x in Ω, B.principalIntegrand u v x + B.c x * u x * v x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.bilin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.bilin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.bilin ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.bilin

def IsSmoothWeakSolution {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (u f : E → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) u ∧
  ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
    B.bilin u φ = ∫ x in Ω, f x * φ x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.IsSmoothWeakSolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.IsSmoothWeakSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.IsSmoothWeakSolution ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.IsSmoothWeakSolution

theorem principalIntegrand_symm {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (u v : E → ℝ) (x : E) :
    B.principalIntegrand u v x = B.principalIntegrand v u x := by
  classical
  unfold principalIntegrand
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [B.symm x j i]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.principalIntegrand_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.principalIntegrand_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.principalIntegrand_symm ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.principalIntegrand_symm

theorem continuous_principalIntegrand {Ω : Set E}
    (B : SmoothEllipticBilinearForm d Ω) {u v : E → ℝ}
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) :
    Continuous (B.principalIntegrand u v) := by
  classical
  unfold principalIntegrand
  refine continuous_finsetSum _ ?_
  intro i _
  refine continuous_finsetSum _ ?_
  intro j _
  refine ((B.continuous_a i j).mul ?_).mul ?_
  · exact (hu.continuous_fderiv (by simp)).clm_apply continuous_const
  · exact (hv.continuous_fderiv (by simp)).clm_apply continuous_const

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.continuous_principalIntegrand then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.continuous_principalIntegrand"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.continuous_principalIntegrand ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.continuous_principalIntegrand

theorem continuous_bilin_integrand {Ω : Set E}
    (B : SmoothEllipticBilinearForm d Ω) {u v : E → ℝ}
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) :
    Continuous (fun x => B.principalIntegrand u v x + B.c x * u x * v x) :=
  (B.continuous_principalIntegrand hu hv).add
    ((B.continuous_c.mul hu.continuous).mul hv.continuous)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.continuous_bilin_integrand then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.continuous_bilin_integrand"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.continuous_bilin_integrand ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.continuous_bilin_integrand

def gradientVec (u : E → ℝ) (x : E) : E :=
  WithLp.toLp 2 (fun i : Fin d => (fderiv ℝ u x) (EuclideanSpace.single i 1))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.gradientVec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.gradientVec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.gradientVec ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.gradientVec

theorem principalIntegrand_self_eq_inner {Ω : Set E}
    (B : SmoothEllipticBilinearForm d Ω) (u : E → ℝ) (x : E) :
    B.principalIntegrand u u x =
      ⟪gradientVec u x, DeGiorgi.matMulE (B.a x) (gradientVec u x)⟫_ℝ := by
  classical
  set ξ : E := gradientVec u x with hξ
  set V : Fin d → ℝ := fun i => (fderiv ℝ u x) (EuclideanSpace.single i 1) with hV
  have h_inner :
      ⟪ξ, DeGiorgi.matMulE (B.a x) ξ⟫_ℝ =
        (fun j => (B.a x).mulVec V j) ⬝ᵥ V := by
    have hξofLp : ξ.ofLp = V := by simp [hξ, hV, gradientVec]
    have hmatofLp : (DeGiorgi.matMulE (B.a x) ξ).ofLp = (B.a x).mulVec V := by
      rw [DeGiorgi.matMulE_ofLp, hξofLp]
    change (DeGiorgi.matMulE (B.a x) ξ).ofLp ⬝ᵥ _root_.Star.star ξ.ofLp =
      (fun j => (B.a x).mulVec V j) ⬝ᵥ V
    rw [hmatofLp, hξofLp]
    change (B.a x).mulVec V ⬝ᵥ (_root_.Star.star V) = (B.a x).mulVec V ⬝ᵥ V
    rfl
  rw [h_inner]
  unfold principalIntegrand
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro j _
  change ∑ i, B.a x i j * V i * V j = (B.a x).mulVec V j * V j
  rw [show ((B.a x).mulVec V) j = ∑ i, B.a x j i * V i from rfl]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [B.symm x i j]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.principalIntegrand_self_eq_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.principalIntegrand_self_eq_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.principalIntegrand_self_eq_inner ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.principalIntegrand_self_eq_inner

theorem principalIntegrand_self_ge {Ω : Set E}
    (B : SmoothEllipticBilinearForm d Ω) (u : E → ℝ)
    {x : E} (hx : x ∈ Ω) :
    B.lam * ‖gradientVec u x‖ ^ 2 ≤
      B.principalIntegrand u u x := by
  rw [principalIntegrand_self_eq_inner]
  exact B.coercive x hx (gradientVec u x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.principalIntegrand_self_ge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.principalIntegrand_self_ge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.principalIntegrand_self_ge ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.principalIntegrand_self_ge

omit [NeZero d] in
theorem gradientVec_norm_sq_eq_sum (u : E → ℝ) (x : E) :
    ‖gradientVec u x‖ ^ 2 =
      ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1)) ^ 2 := by
  unfold gradientVec
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl ?_
  intro i _
  change ‖(fderiv ℝ u x) (EuclideanSpace.single i 1)‖ ^ 2 = _
  rw [Real.norm_eq_abs, sq_abs]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.gradientVec_norm_sq_eq_sum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.gradientVec_norm_sq_eq_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.gradientVec_norm_sq_eq_sum ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.gradientVec_norm_sq_eq_sum

theorem bilin_integrand_self_ge {Ω : Set E}
    (B : SmoothEllipticBilinearForm d Ω) (u : E → ℝ)
    {x : E} (hx : x ∈ Ω) :
    B.lam * ‖gradientVec u x‖ ^ 2 + B.c x * u x * u x ≤
      B.principalIntegrand u u x + B.c x * u x * u x := by
  have h := B.principalIntegrand_self_ge u hx
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.bilin_integrand_self_ge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.bilin_integrand_self_ge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.bilin_integrand_self_ge ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.bilin_integrand_self_ge

end SmoothEllipticBilinearForm

omit [NeZero d] in
theorem diffQuot_mul
    (i : Fin d) (h : ℝ) (f g : E → ℝ) :
    DifferentialGeometry.Analysis.Sobolev.diffQuot i h (fun x => f x * g x) =
      fun x =>
        (DifferentialGeometry.Analysis.Sobolev.translate i h f x) *
            (DifferentialGeometry.Analysis.Sobolev.diffQuot i h g x) +
          (DifferentialGeometry.Analysis.Sobolev.diffQuot i h f x) * g x := by
  ext x
  by_cases hh : h = 0
  · subst hh
    simp [DifferentialGeometry.Analysis.Sobolev.diffQuot,
          DifferentialGeometry.Analysis.Sobolev.translate]
  · simp only [DifferentialGeometry.Analysis.Sobolev.diffQuot,
               DifferentialGeometry.Analysis.Sobolev.translate, hh, ↓reduceIte]
    field_simp
    ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.diffQuot_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.diffQuot_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.diffQuot_mul ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.diffQuot_mul

omit [NeZero d] in
theorem diffQuot_coeff_apply
    (k : Fin d) (h : ℝ) (a v : E → ℝ) (x : E) :
    DifferentialGeometry.Analysis.Sobolev.diffQuot k h (fun y => a y * v y) x =
      DifferentialGeometry.Analysis.Sobolev.translate k h a x *
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h v x +
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h a x * v x := by
  have h := diffQuot_mul (d := d) k h a v
  exact congrArg (fun f : E → ℝ => f x) h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.diffQuot_coeff_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.diffQuot_coeff_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.diffQuot_coeff_apply ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.diffQuot_coeff_apply

end DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
