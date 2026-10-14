import Submission.DifferentialGeometry.Analysis.Integration.Lp.BoundedComposition
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.LipschitzWitness
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.WeakLimit
import Submission.DifferentialGeometry.Analysis.Integration.Lp.QuadraticLowerSemicontinuity
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.DirichletEnergy.WeakLowerSemicontinuity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section

open _root_.Filter _root_.Submission.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ENNReal _root_.NNReal _root_.Topology

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_memW1pWitness_comp_of_ae_tendsto_of_lipschitz
    {X : Type*} [TopologicalSpace X] {Ω : Set E}
    [_root_.MeasureTheory.IsFiniteMeasure (volume.restrict Ω)]
    {Φ : X → ℝ} (hΦ : Continuous Φ) {D : ℝ} (hD : ∀ p, ‖Φ p‖ ≤ D)
    (U : ℕ → E → X) (v : E → X)
    (hLip : ∀ n, ∃ K : ℝ≥0, LipschitzWith K (Φ ∘ U n))
    (hae : ∀ᵐ x ∂volume.restrict Ω,
      _root_.Filter.Tendsto (fun n => U n x) _root_.Filter.atTop (𝓝 (v x)))
    {B : ℝ} (hB : ∀ n, (∫ x in Ω, ‖fderiv ℝ (Φ ∘ U n) x‖ ^ 2) ≤ B) :
    ∃ (hs : ∀ n, DeGiorgi.MemW1pWitness 2 (Φ ∘ U n) Ω)
      (σ : ℕ → ℕ) (hv : DeGiorgi.MemW1pWitness 2 (Φ ∘ v) Ω),
      (∀ n x i, (hs n).weakGrad x i =
        fderiv ℝ (Φ ∘ U n) x (EuclideanSpace.single i 1)) ∧
      StrictMono σ ∧
      _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => Φ (U n x) - Φ (v x))
        2 (volume.restrict Ω)) _root_.Filter.atTop (𝓝 0) ∧
      ‖DeGiorgi.gradLpOfWitness hv‖ ≤ Real.sqrt B ∧
      (∀ z : _root_.MeasureTheory.Lp E 2 (volume.restrict Ω),
        _root_.Filter.Tendsto (fun n => _root_.Inner.inner ℝ (DeGiorgi.gradLpOfWitness (hs (σ n))) z) _root_.Filter.atTop
          (𝓝 (_root_.Inner.inner ℝ (DeGiorgi.gradLpOfWitness hv) z))) ∧
      (∫ x in Ω, ‖hv.weakGrad x‖ ^ 2) ≤
        liminf (fun n => ∫ x in Ω, ‖fderiv ℝ (Φ ∘ U n) x‖ ^ 2) atTop := by
  choose K hK using hLip
  have hfm (n : ℕ) : _root_.MeasureTheory.MemLp (Φ ∘ U n) 2 (volume.restrict Ω) :=
    MemLp.of_bound (hK n).continuous.aestronglyMeasurable D
      (Eventually.of_forall fun x => hD (U n x))
  have hdfm (n : ℕ) : _root_.MeasureTheory.MemLp (fderiv ℝ (Φ ∘ U n)) 2 (volume.restrict Ω) :=
    MemLp.of_bound (measurable_fderiv ℝ (Φ ∘ U n)).aestronglyMeasurable (K n)
      (Eventually.of_forall fun x => norm_fderiv_le_of_lipschitz ℝ (hK n))
  choose hs hrep hnorm using fun n =>
    exists_memW1pWitness_fderiv_of_lipschitz (hK n) (hfm n) (hdfm n)
  have hbound (n : ℕ) : ‖DeGiorgi.gradLpOfWitness (hs n)‖ ≤ Real.sqrt B := by
    rw [DeGiorgi.gradLpOfWitness, Lp.norm_toLp, hnorm n]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (Analysis.Integration.eLpNorm_two_le_of_integral_norm_sq_le (hdfm n) (hB n))).trans_eq
      (ENNReal.toReal_ofReal (Real.sqrt_nonneg B))
  obtain ⟨hvm, hL2⟩ := MeasureTheory.memLp_and_tendsto_eLpNorm_comp_of_ae_tendsto_of_bounded
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    hΦ hD (fun n => (hfm n).aestronglyMeasurable) hae
  let q : ℕ → ℝ := fun n => ∫ x in Ω, ‖fderiv ℝ (Φ ∘ U n) x‖ ^ 2
  have hqlo : _root_.Filter.IsBoundedUnder (· ≥ ·) _root_.Filter.atTop q := by
    refine ⟨0, ?_⟩
    change ∀ᶠ n in _root_.Filter.atTop, 0 ≤ q n
    exact Eventually.of_forall fun n => _root_.MeasureTheory.integral_nonneg fun x => sq_nonneg _
  have hqhi : _root_.Filter.IsCoboundedUnder (· ≥ ·) _root_.Filter.atTop q :=
    _root_.Filter.isCoboundedUnder_ge_of_eventually_le _root_.Filter.atTop (Eventually.of_forall hB)
  obtain ⟨ρ, hρq, hρ⟩ := exists_seq_tendsto_liminf hqhi hqlo
  obtain ⟨θ, hθ, hρθ⟩ := _root_.Filter.strictMono_subseq_of_tendsto_atTop hρ
  let τ := ρ ∘ θ
  have hτ : StrictMono τ := hρθ
  have hτq : _root_.Filter.Tendsto (fun n => q (τ n)) _root_.Filter.atTop (𝓝 (_root_.Filter.liminf q _root_.Filter.atTop)) :=
    hρq.comp hθ.tendsto_atTop
  obtain ⟨ψ, hv, hψ, hvbound, hweak⟩ :=
    exists_memW1pWitness_of_tendsto_L2_norm_bounded
      (fun n => hs (τ n)) hvm (fun n => hbound (τ n)) (hL2.comp hτ.tendsto_atTop)
  let σ := τ ∘ ψ
  have hσ : StrictMono σ := hτ.comp hψ
  refine ⟨hs, σ, hv, hrep, hσ, hL2, hvbound, hweak, ?_⟩
  let Q : E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ
  have hdual (F : _root_.MeasureTheory.Lp E 2 (volume.restrict Ω) →L[ℝ] ℝ) :
      _root_.Filter.Tendsto (fun n => F (DeGiorgi.gradLpOfWitness (hs (σ n)))) _root_.Filter.atTop
        (𝓝 (F (DeGiorgi.gradLpOfWitness hv))) := by
    have hF (w : _root_.MeasureTheory.Lp E 2 (volume.restrict Ω)) :
        F w = _root_.Inner.inner ℝ w ((_root_.InnerProductSpace.toDual ℝ _).symm F) := by
      rw [real_inner_comm, _root_.InnerProductSpace.toDual_symm_apply]
    simpa only [hF, σ, Function.comp_apply] using
      hweak ((_root_.InnerProductSpace.toDual ℝ _).symm F)
  have hlsc := integral_quadratic_le_liminf_of_weak (μ := volume.restrict Ω)
    (fun _ _ => Q) (fun _ => Q)
    (fun _ _ _ => _root_.MeasureTheory.aestronglyMeasurable_const) (fun _ _ => _root_.MeasureTheory.aestronglyMeasurable_const)
    (fun _ => ‖Q‖) ‖Q‖ (fun _ => Eventually.of_forall fun _ => le_rfl)
    (Eventually.of_forall fun _ => le_rfl)
    (fun δ hδ => Eventually.of_forall fun _ => Eventually.of_forall fun _ => by
      have he : Q - Q = 0 := by
        ext x y
        change Q x y - Q x y = 0
        exact sub_self _
      rw [he]
      exact (ContinuousLinearMap.opNorm_zero : ‖(0 : E →L[ℝ] E →L[ℝ] ℝ)‖ = 0).le.trans hδ.le)
    (fun _ => Eventually.of_forall fun _ x => by
      change 0 ≤ _root_.Inner.inner ℝ x x
      exact real_inner_self_nonneg)
    (fun n => DeGiorgi.gradLpOfWitness (hs (σ n))) (DeGiorgi.gradLpOfWitness hv) hdual
  have hQ (w : _root_.MeasureTheory.Lp E 2 (volume.restrict Ω)) :
      (∫ x in Ω, Q (w x) (w x)) = ‖w‖ ^ 2 := by
    change _root_.Inner.inner ℝ w w = ‖w‖ ^ 2
    exact real_inner_self_eq_norm_sq w
  have henergy (n : ℕ) : ‖DeGiorgi.gradLpOfWitness (hs n)‖ ^ 2 = q n := by
    rw [DeGiorgi.gradLpOfWitness, Lp.norm_toLp, hnorm n]
    simpa only [q, _root_.MeasureTheory.eLpNorm_norm] using
      (Analysis.Integration.integral_sq_eq_l2 (hdfm n).norm).symm
  simp only [hQ, henergy] at hlsc
  have hσq : _root_.Filter.Tendsto (fun n => q (σ n)) _root_.Filter.atTop (𝓝 (_root_.Filter.liminf q _root_.Filter.atTop)) := by
    simpa only [σ, Function.comp_def] using hτq.comp hψ.tendsto_atTop
  rw [hσq.liminf_eq] at hlsc
  rw [norm_gradLpOfWitness_sq_eq_integral] at hlsc
  exact hlsc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_memW1pWitness_comp_of_ae_tendsto_of_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_memW1pWitness_comp_of_ae_tendsto_of_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_memW1pWitness_comp_of_ae_tendsto_of_lipschitz ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_memW1pWitness_comp_of_ae_tendsto_of_lipschitz

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

end
