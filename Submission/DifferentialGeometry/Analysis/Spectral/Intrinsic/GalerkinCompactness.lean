import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformConvergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.Set
open scoped _root_.BigOperators _root_.BoundedContinuousFunction _root_.NNReal _root_.Topology

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

theorem fatou_sq_mass {ι : Type*} (S : ℕ → Finset ι)
    (hS : _root_.Filter.Tendsto S _root_.Filter.atTop _root_.Filter.atTop) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (v : ℕ → ι → ℝ) (vlim : ι → ℝ)
    (hconv : ∀ i, _root_.Filter.Tendsto (fun N => v N i) _root_.Filter.atTop (𝓝 (vlim i)))
    (B : ℝ) (hbound : ∀ N, ∑ i ∈ S N, w i * (v N i) ^ 2 ≤ B) :
    Summable (fun i => w i * (vlim i) ^ 2) ∧
      ∑' i, w i * (vlim i) ^ 2 ≤ B := by
  have hnn : ∀ i, 0 ≤ w i * (vlim i) ^ 2 :=
    fun i => mul_nonneg (hw i) (sq_nonneg _)
  have hpartial : ∀ K : Finset ι, ∑ i ∈ K, w i * (vlim i) ^ 2 ≤ B := by
    intro K
    have hlim : _root_.Filter.Tendsto (fun N => ∑ i ∈ K, w i * (v N i) ^ 2) _root_.Filter.atTop
        (𝓝 (∑ i ∈ K, w i * (vlim i) ^ 2)) := by
      refine tendsto_finsetSum K (fun i _ => ?_)
      exact ((hconv i).pow 2).const_mul (w i)
    have hev : ∀ᶠ N in _root_.Filter.atTop, ∑ i ∈ K, w i * (v N i) ^ 2 ≤ B := by
      have hsub : ∀ᶠ N in _root_.Filter.atTop, K ≤ S N := hS.eventually_ge_atTop K
      filter_upwards [hsub] with N hKN
      have hmono : ∑ i ∈ K, w i * (v N i) ^ 2 ≤
          ∑ i ∈ S N, w i * (v N i) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hKN
          (fun i _ _ => mul_nonneg (hw i) (sq_nonneg _))
      exact hmono.trans (hbound N)
    exact le_of_tendsto hlim hev
  exact ⟨summable_of_sum_le hnn hpartial, Real.tsum_le_of_sum_le hnn hpartial⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.fatou_sq_mass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.fatou_sq_mass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.fatou_sq_mass ``Submission.DifferentialGeometry.Analysis.Spectral.fatou_sq_mass

theorem right_lipschitz {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f f' : ℝ → F} {a b : ℝ} {K : ℝ≥0}
    (hf : ContinuousOn f (_root_.Set.Icc a b))
    (hf' : ∀ x ∈ _root_.Set.Ico a b, HasDerivWithinAt f (f' x) (_root_.Set.Ici x) x)
    (hbound : ∀ x ∈ _root_.Set.Ico a b, ‖f' x‖ ≤ (K : ℝ)) :
    LipschitzOnWith K f (_root_.Set.Icc a b) := by
  refine LipschitzOnWith.of_dist_le_mul (fun x hx y hy => ?_)
  rcases le_total x y with hxy | hyx
  · have hcont : ContinuousOn f (_root_.Set.Icc x y) := by
      refine hf.mono (fun z hz => ?_)
      exact ⟨hx.1.trans hz.1, hz.2.trans hy.2⟩
    have hderiv : ∀ z ∈ _root_.Set.Ico x y, HasDerivWithinAt f (f' z) (_root_.Set.Ici z) z := by
      intro z hz
      exact hf' z ⟨hx.1.trans hz.1, hz.2.trans_le hy.2⟩
    have hnorm : ∀ z ∈ _root_.Set.Ico x y, ‖f' z‖ ≤ (K : ℝ) := by
      intro z hz
      exact hbound z ⟨hx.1.trans hz.1, hz.2.trans_le hy.2⟩
    have hseg := norm_image_sub_le_of_norm_deriv_right_le_segment
      hcont hderiv hnorm y (right_mem_Icc.2 hxy)
    simpa only [dist_eq_norm, norm_sub_rev, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.2 hxy), neg_sub] using hseg
  · have hcont : ContinuousOn f (_root_.Set.Icc y x) := by
      refine hf.mono (fun z hz => ?_)
      exact ⟨hy.1.trans hz.1, hz.2.trans hx.2⟩
    have hderiv : ∀ z ∈ _root_.Set.Ico y x, HasDerivWithinAt f (f' z) (_root_.Set.Ici z) z := by
      intro z hz
      exact hf' z ⟨hy.1.trans hz.1, hz.2.trans_le hx.2⟩
    have hnorm : ∀ z ∈ _root_.Set.Ico y x, ‖f' z‖ ≤ (K : ℝ) := by
      intro z hz
      exact hbound z ⟨hy.1.trans hz.1, hz.2.trans_le hx.2⟩
    have hseg := norm_image_sub_le_of_norm_deriv_right_le_segment
      hcont hderiv hnorm x (right_mem_Icc.2 hyx)
    simpa only [dist_eq_norm, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.2 hyx)] using hseg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.right_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.right_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.right_lipschitz ``Submission.DifferentialGeometry.Analysis.Spectral.right_lipschitz

theorem galerkin_subseq {ι : Type*} [Countable ι] {τ : ℝ} (hτ : 0 ≤ τ)
    (u : ℕ → ℝ → ι → ℝ) (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (L : ι → ℝ≥0)
    (hbd : ∀ N t, t ∈ _root_.Set.Icc (0 : ℝ) τ → ∀ i, |u N t i| ≤ C i)
    (hlip : ∀ N i, LipschitzOnWith (L i) (fun t => u N t i) (_root_.Set.Icc (0 : ℝ) τ)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ ulim : ℝ → ι → ℝ,
        (∀ i, Continuous (fun t => ulim t i)) ∧
          ∀ i, TendstoUniformlyOn (fun n t => u (φ n) t i)
            (fun t => ulim t i) _root_.Filter.atTop (_root_.Set.Icc (0 : ℝ) τ) := by
  classical
  let J : Set ℝ := _root_.Set.Icc (0 : ℝ) τ
  let : CompactSpace J := isCompact_iff_compactSpace.mp (by
    simpa only [J] using (_root_.CompactIccSpace.isCompact_Icc : IsCompact (_root_.Set.Icc (0 : ℝ) τ)))
  let f : ι → ℕ → (J →ᵇ ℝ) := fun i N =>
    BoundedContinuousFunction.mkOfCompact
      ⟨fun t : J => u N t i, by
        change Continuous ((_root_.Set.Icc (0 : ℝ) τ).domRestrict fun t => u N t i)
        exact (hlip N i).to_restrict.continuous⟩
  have hvalues (i : ι) : ∀ (g : J →ᵇ ℝ) (t : J),
      g ∈ _root_.Set.range (f i) → g t ∈ _root_.Set.Icc (-C i) (C i) := by
    rintro g t ⟨N, rfl⟩
    have hu := hbd N (t : ℝ) (by simpa only [J] using t.2) i
    have hu' : |u N (t : ℝ) i| ≤ _root_.Max.max (C i) 0 := hu.trans (le_max_left _ _)
    change -C i ≤ u N (t : ℝ) i ∧ u N (t : ℝ) i ≤ C i
    simpa only [max_eq_left (hC i)] using abs_le.mp hu'
  have hequicont (i : ι) :
      Equicontinuous ((↑) : (_root_.Set.range (f i)) → J → ℝ) := by
    refine Metric.equicontinuous_of_continuity_modulus
      (fun s => (L i : ℝ) * s) ?_ _ ?_
    · have ht : _root_.Filter.Tendsto (fun s : ℝ => (L i : ℝ) * s) (𝓝 0)
          (𝓝 ((L i : ℝ) * 0)) := tendsto_const_nhds.mul _root_.Filter.tendsto_id
      simpa only [_root_.MulZeroClass.mul_zero] using ht
    · rintro x y ⟨g, hg⟩
      rcases hg with ⟨N, rfl⟩
      have hdist := (hlip N i).to_restrict.dist_le_mul x y
      change _root_.Dist.dist (u N (x : ℝ) i) (u N (y : ℝ) i) ≤
        (L i : ℝ) * _root_.Dist.dist x y
      exact hdist
  let K : ι → Set (J →ᵇ ℝ) := fun i => closure (_root_.Set.range (f i))
  have hK (i : ι) : IsCompact (K i) := by
    simpa only [K] using
      BoundedContinuousFunction.arzela_ascoli (_root_.Set.Icc (-C i) (C i)) _root_.CompactIccSpace.isCompact_Icc
        (_root_.Set.range (f i)) (hvalues i) (hequicont i)
  let F : ℕ → (∀ i, J →ᵇ ℝ) := fun N i => f i N
  have hF (N : ℕ) : F N ∈ Set.pi _root_.Set.univ K := by
    intro i _
    change f i N ∈ closure (_root_.Set.range (f i))
    exact subset_closure (_root_.Set.mem_range_self N)
  have hprod : IsCompact (Set.pi _root_.Set.univ K) := isCompact_univ_pi hK
  obtain ⟨g, _, φ, hφ, hg⟩ := hprod.tendsto_subseq hF
  let ulim : ℝ → ι → ℝ := fun t i => _root_.Set.IccExtend hτ (fun x : J => g i x) t
  refine ⟨φ, hφ, ulim, ?_, ?_⟩
  · intro i
    simpa only [ulim, J] using (g i).continuous.Icc_extend'
  · intro i
    have hcoord : _root_.Filter.Tendsto (fun n => f i (φ n)) _root_.Filter.atTop (𝓝 (g i)) := by
      rw [tendsto_pi_nhds] at hg
      simpa only [Function.comp_apply, F] using hg i
    have huniform : TendstoUniformly (fun (n : ℕ) (t : J) => u (φ n) t i)
        (fun t : J => g i t) atTop := by
      have h := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hcoord
      change TendstoUniformly (fun (n : ℕ) (t : J) => u (φ n) t i)
        (fun t : J => g i t) _root_.Filter.atTop at h
      exact h
    rw [tendstoUniformlyOn_iff_restrict]
    have hlim : J.domRestrict (fun t => ulim t i) = fun t : J => g i t := by
      funext t
      change ulim (t : ℝ) i = g i t
      exact _root_.Set.IccExtend_val hτ (fun x : J => g i x) t
    rw [hlim]
    exact huniform

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.galerkin_subseq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.galerkin_subseq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.galerkin_subseq ``Submission.DifferentialGeometry.Analysis.Spectral.galerkin_subseq

end Spectral
end Analysis
end DifferentialGeometry

end
