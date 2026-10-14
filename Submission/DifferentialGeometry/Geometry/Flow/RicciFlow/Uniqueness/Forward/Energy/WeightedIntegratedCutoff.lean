import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Energy.WeightedCutoff
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Energy.CutoffTimeDerivative
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Energy.CutoffContinuity
import Submission.DifferentialGeometry.Analysis.Integration.CompactExhaustionDerivative
import Submission.DifferentialGeometry.Analysis.ODE.Gronwall.DominatedSubsolutions

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Analysis _root_.Submission.DifferentialGeometry.Analysis.ODE
open scoped _root_.Topology
open _root_.Submission.DifferentialGeometry.Geometry.Connection _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Integral.Measure _root_.Submission.DifferentialGeometry.Integral.Connection
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [I.Boundaryless] [SigmaCompactSpace M]

theorem forward_uniqueness_weighted_energy_sub_le_integral_on_Ioo_of_uniform_bounds
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M)
    {a b : ℝ}
    (hjoint₁ : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₁ p.1) α p.2 i j)
        (_root_.Set.Ioo a b ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet))
    (hjoint₂ : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₂ p.1) α p.2 i j)
        (_root_.Set.Ioo a b ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet))
    (hpde₁ : ∀ t ∈ _root_.Set.Ioo a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s => (g₁ s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g₁ t) x v w) (_root_.Set.Ici a) t)
    (hpde₂ : ∀ t ∈ _root_.Set.Ioo a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s => (g₂ s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g₂ t) x v w) (_root_.Set.Ici a) t)
    {C R₁ R₂ D₁ D₂ : ℝ} (hC : 1 ≤ C)
    (hEquiv : ∀ t ∈ _root_.Set.Ioo a b, ∀ x : M, ∀ v : TangentSpace I x,
      C⁻¹ * (g₁ t).inner x v v ≤ (g₂ t).inner x v v ∧
        (g₂ t).inner x v v ≤ C * (g₁ t).inner x v v)
    (hR₁ : ∀ t ∈ _root_.Set.Ioo a b, ∀ x : M,
      normSq0S (I := I) (g₁ t) x 4 (metricRm04At (I := I) (g₁ t) x) ≤ R₁)
    (hR₂ : ∀ t ∈ _root_.Set.Ioo a b, ∀ x : M,
      normSq0S (I := I) (g₂ t) x 4 (metricRm04At (I := I) (g₂ t) x) ≤ R₂)
    (hD₁ : ∀ t ∈ _root_.Set.Ioo a b, ∀ x : M, normSq0S (I := I) (g₂ t) x 5
      (metricNabla0S (I := I) (g₂ t)
        (CovariantDerivative.rm04Section (I := I) (g₂ t) (metricCov (I := I) (g₂ t))
          (metricCov_smooth (I := I) (g₂ t))) x) ≤ D₁)
    (hD₂ : ∀ t ∈ _root_.Set.Ioo a b, ∀ x : M, normSq0S (I := I) (g₂ t) x 6
      (metricNabla0S (I := I) (g₂ t) (metricNabla0S (I := I) (g₂ t)
        (CovariantDerivative.rm04Section (I := I) (g₂ t) (metricCov (I := I) (g₂ t))
          (metricCov_smooth (I := I) (g₂ t)))) x) ≤ D₂)
    (η : C^∞⟮I, M; ℝ⟯) {A : ℝ} (hA : 0 ≤ A)
    (hηgrad : ∀ t ∈ _root_.Set.Ioo a b, ∀ x : M,
      normSq0S (I := I) (g₁ t) x 1 (differential1FormFun (I := I) η x) ≤ A * η x ^ 2)
    (Kex : CompactExhaustion M) (χ : ℕ → C^∞⟮I, M; ℝ⟯)
    (hχsupport : ∀ n, HasCompactSupport (χ n : M → ℝ))
    (hχone : ∀ n, ∀ x ∈ Kex n, χ n x = 1)
    (hχrange : ∀ n x, |χ n x| ≤ 1) {L : ℝ}
    (hχgrad : ∀ n, ∀ t ∈ _root_.Set.Ioo a b, ∀ x : M,
      normSq0S (I := I) (g₁ t) x 1 (differential1FormFun (I := I) (χ n) x) ≤ L)
    (hden : ∀ t ∈ _root_.Set.Ioo a b,
      Integrable (fun x => η x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x)
        (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hEint : ∀ c ∈ _root_.Set.Ioo a b,
      IntervalIntegrable (fun t => ∫ x, η x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x
        ∂riemannianMeasureFamily (I := I) (M := M) g₁ t) _root_.MeasureTheory.MeasureSpace.volume a c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ _root_.Set.Ioo a b, ∀ c ∈ _root_.Set.Ico s b,
      (∫ x, η x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ c x
        ∂riemannianMeasureFamily (I := I) (M := M) g₁ c) -
      (∫ x, η x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ s x
        ∂riemannianMeasureFamily (I := I) (M := M) g₁ s) ≤
        K * ∫ t in s..c, ∫ x, η x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x
          ∂riemannianMeasureFamily (I := I) (M := M) g₁ t := by
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  obtain ⟨K, hK, henergy⟩ := forward_uniqueness_weighted_cutoff_energy_uniform_bound_on_Ioo
    (I := I) g₁ g₂ hjoint₁ hjoint₂ hpde₁ hpde₂ hC hEquiv hR₁ hR₂ hD₁ hD₂ η hA hηgrad
  let S := fun t => forwardUniquenessSfield (I := I) g₁ g₂ t
  let d := fun t x => η x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x
  let e := fun t => ∫ x, d t x ∂riemannianMeasureFamily g₁ t
  let q := fun n t x => normSq0S (I := I) (g₁ t) x 1
    (differential1FormFun (I := I) (χ n) x)
  let u := fun n t => ∫ x, χ n x ^ 2 * d t x ∂riemannianMeasureFamily g₁ t
  let r := fun n t => 20 * ∫ x, q n t x * d t x ∂riemannianMeasureFamily g₁ t
  let ψ : ℕ → C^∞⟮I, M; ℝ⟯ := fun n => η * χ n
  have hψ (n : ℕ) : HasCompactSupport (ψ n : M → ℝ) := by
    apply HasCompactSupport.mono (hχsupport n)
    intro x hx hzero
    apply hx
    simp [ψ, hzero]
  have hu (n : ℕ) : u n = fun t => ∫ x, (ψ n x) ^ 2 *
      forwardUniqueDensity (I := I) g₁ g₂ t x ∂riemannianMeasureFamily g₁ t := by
    funext t
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [] with x
    simp only [ψ, ContMDiffMap.coe_mul, Pi.mul_apply, d]
    ring
  have hd0 (t : ℝ) (x : M) : 0 ≤ d t x :=
    mul_nonneg (sq_nonneg _) (density_nonneg (I := I) g₁ g₂ t x)
  have hq0 (n : ℕ) (t : ℝ) (x : M) : 0 ≤ q n t x :=
    normSq0S_nonneg (I := I) (g₁ t) x 1 _
  have hqjoint (n : ℕ) : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => q n p.1 p.2) (_root_.Set.Ioo a b ×ˢ (_root_.Set.univ : Set M)) := by
    apply normSq0S_jointContMDiffOn (I := I) g₁
      (fun _ x => differential1FormFun (I := I) (χ n) x) hjoint₁
    intro α slots t ht
    have hf := tensor0SField_eval_cmdAt_slots (I := I)
      (duSec (I := I) (χ n) (χ n).contMDiff)
      (fun i y => chartBasisVecFiber (I := I) α (slots i) y)
      (fun i => (chartBasisVec_contMDiffOn (I := I) α (slots i)).contMDiffAt
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds
          (_root_.FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) α)))
    have hsnd : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => p.2) (t, α) :=
      contMDiffAt_snd
    exact (hf.comp (t, α) hsnd).contMDiffWithinAt
  have hrcont (n : ℕ) : ContinuousOn (r n) (_root_.Set.Ioo a b) := by
    have hf : ContinuousOn (fun p : ℝ × M => q n p.1 p.2 * d p.1 p.2)
        (_root_.Set.Ioo a b ×ˢ (_root_.Set.univ : Set M)) :=
      (hqjoint n).continuousOn.mul
        (((η.contMDiff.continuous.comp continuous_snd).pow 2).continuousOn.mul
          (dens_jointContMDiffOn (I := I) g₁ g₂ hjoint₁ hjoint₂).continuousOn)
    have hc := continuousOn_integral_riemannianVolumeMeasure_of_compact_support
      (I := I) g₁ (fun α i j => (hjoint₁ α i j).continuousOn)
      (fun t x => q n t x * d t x) hf (hχsupport n) ?_
    · exact hc.const_mul 20
    · intro t ht x hx
      have heq : (χ n : M → ℝ) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        filter_upwards [(isClosed_tsupport _).isOpen_compl.mem_nhds hx] with y hy
        exact image_eq_zero_of_notMem_tsupport hy
      have hd : mvfderiv (I := I) (χ n : M → ℝ) x = 0 := by
        ext v
        rw [mvfderiv_real_eq_mfderiv (I := I),
          heq.mfderiv_eq (I := I) (I' := 𝓘(ℝ, ℝ)), mfderiv_const]
        rfl
      have hdf : differential1FormFun (I := I) (χ n) x = 0 := by
        ext v
        simp only [differential1FormFun, hd]
        rfl
      have hnzero := (normSq0S_eq_zero_iff (I := I) (g₁ t) x 1 0).2 rfl
      simp only [q, hdf, hnzero, _root_.MulZeroClass.zero_mul]
  have hu0 (n : ℕ) (t : ℝ) : 0 ≤ u n t := _root_.MeasureTheory.integral_nonneg fun x =>
    mul_nonneg (sq_nonneg (χ n x)) (hd0 t x)
  have hr0 (n : ℕ) (t : ℝ) : 0 ≤ r n t :=
    mul_nonneg (by norm_num) (_root_.MeasureTheory.integral_nonneg fun x => mul_nonneg (hq0 n t x) (hd0 t x))
  have hule (n : ℕ) (t : ℝ) (ht : t ∈ _root_.Set.Ioo a b) :
      u n t ≤ e t := by
    apply _root_.MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (hd0 t x))
      (hden t ht)
    filter_upwards [] with x
    have hsq : χ n x ^ 2 ≤ 1 := by nlinarith [abs_nonneg (χ n x), sq_abs (χ n x), hχrange n x]
    exact mul_le_of_le_one_left (hd0 t x) hsq
  have hrle (n : ℕ) (t : ℝ) (ht : t ∈ _root_.Set.Ioo a b) :
      r n t ≤ (20 * |L|) * e t := by
    have hi : (∫ x, q n t x * d t x ∂riemannianMeasureFamily g₁ t) ≤
        ∫ x, |L| * d t x ∂riemannianMeasureFamily g₁ t := by
      apply _root_.MeasureTheory.integral_mono_of_nonneg
        (Eventually.of_forall fun x => mul_nonneg (hq0 n t x) (hd0 t x)) ((hden t ht).const_mul |L|)
      filter_upwards [] with x
      exact mul_le_mul_of_nonneg_right ((hχgrad n t ht x).trans (le_abs_self L))
        (hd0 t x)
    rw [_root_.MeasureTheory.integral_const_mul] at hi
    exact (mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 20)).trans_eq (mul_assoc _ _ _).symm
  have hrto (t : ℝ) (ht : t ∈ _root_.Set.Ioo a b) : _root_.Filter.Tendsto (fun n => r n t) _root_.Filter.atTop (𝓝 0) := by
    have h := tendsto_integral_normSq0S_differential_mul_of_compactExhaustion
      (I := I) Kex (g₁ t) χ hχone
      (fun n => Eventually.of_forall fun x => hχgrad n t ht x) (hden t ht)
    simpa only [_root_.MulZeroClass.mul_zero] using h.const_mul 20
  refine ⟨K, hK, fun s hs c hc => ?_⟩
  have hca : c ∈ _root_.Set.Ioo a b := ⟨hs.1.trans_le hc.1, hc.2⟩
  have hein : IntervalIntegrable e _root_.MeasureTheory.MeasureSpace.volume s c := (hEint s hs).symm.trans (hEint c hca)
  have hsubinterval : _root_.Set.Icc s c ⊆ _root_.Set.Ioo a b := fun t ht => ⟨hs.1.trans_le ht.1, ht.2.trans_lt hc.2⟩
  have hcont (n : ℕ) : ContinuousOn (u n) (_root_.Set.Icc s c) := by
    rw [hu n]
    exact (forward_uniqueness_cutoff_energy_continuousOn (I := I) g₁ g₂
      (ψ n) (ψ n).contMDiff.continuous (hψ n) hjoint₁ hjoint₂).mono hsubinterval
  apply sub_le_integral_of_dominated_subsolutions hc.1 (u := u)
    (u' := fun n => deriv (u n)) (r := r)
    (G := e)
    (H := fun t => (20 * |L|) * e t)
    hcont
  · intro n t ht
    rw [hu n]
    exact (forward_uniqueness_cutoff_energy_hasDerivAt_on_Ioo (I := I) g₁ g₂ (ψ n)
      (hψ n) hjoint₁ hjoint₂ hpde₁ hpde₂
      ⟨hs.1.trans ht.1, ht.2.trans hc.2⟩).differentiableAt.hasDerivAt.hasDerivWithinAt
  · intro n t ht
    have he := henergy (χ n) (hχsupport n) t ⟨hs.1.trans ht.1, ht.2.trans hc.2⟩
    have hd : 0 ≤ ∫ x, (η x * χ n x) ^ 2 * normSq0S (I := I) (g₁ t) x 5
        (metricNabla0S (I := I) (g₁ t) (S t) x) ∂riemannianMeasureFamily g₁ t :=
      integral_nonneg fun x => mul_nonneg (sq_nonneg _) (normSq0S_nonneg (I := I) (g₁ t) x 5 _)
    have he' : deriv (u n) t ≤ K * u n t -
      (∫ x, (η x * χ n x) ^ 2 * normSq0S (I := I) (g₁ t) x 5
        (metricNabla0S (I := I) (g₁ t) (S t) x) ∂riemannianMeasureFamily g₁ t) + r n t := by
      convert he using 1 <;> simp only [hu n, ψ, ContMDiffMap.coe_mul, Pi.mul_apply, r, q, d, S]
      congr 2
      apply _root_.MeasureTheory.integral_congr_ae
      filter_upwards [] with x
      ring
    linarith only [he', hd]
  · intro n
    exact ((hrcont n).mono hsubinterval).integrableOn_Icc.aestronglyMeasurable
  · exact hein
  · exact hein.const_mul (20 * |L|)
  · intro n
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (hu0 n t)]
    exact hule n t (hsubinterval ht)
  · intro n
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (hr0 n t)]
    exact hrle n t (hsubinterval ht)
  · intro t ht
    exact tendsto_integral_sq_mul_of_compactExhaustion Kex
      (fun n => (χ n).contMDiff.continuous.aestronglyMeasurable)
      (fun n => Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hχrange n x)
      hχone (hden t (hsubinterval ht))
  · filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
    exact hrto t (hsubinterval ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.forward_uniqueness_weighted_energy_sub_le_integral_on_Ioo_of_uniform_bounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.forward_uniqueness_weighted_energy_sub_le_integral_on_Ioo_of_uniform_bounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.forward_uniqueness_weighted_energy_sub_le_integral_on_Ioo_of_uniform_bounds ``Submission.DifferentialGeometry.PDE.RicciFlow.forward_uniqueness_weighted_energy_sub_le_integral_on_Ioo_of_uniform_bounds

end DifferentialGeometry.PDE.RicciFlow
