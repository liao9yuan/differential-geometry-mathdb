import Submission.DifferentialGeometry.External.DeGiorgi.WeakFormulation.SmoothTests
import Submission.DifferentialGeometry.Analysis.InnerProductSpace.WeakCompactness
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Set
open scoped _root_.ENNReal _root_.Topology

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

private theorem tendsto_integral_mul_clm_of_weak
    {P X ι : Type*} [MeasurableSpace P] {μ : _root_.MeasureTheory.Measure P}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {l : Filter ι} {U : ι → _root_.MeasureTheory.Lp X 2 μ} {u : _root_.MeasureTheory.Lp X 2 μ}
    (hU : ∀ F : _root_.MeasureTheory.Lp X 2 μ →L[ℝ] ℝ, _root_.Filter.Tendsto (fun n => F (U n)) l (𝓝 (F u)))
    {φ : P → ℝ} (hφ : _root_.MeasureTheory.MemLp φ 2 μ) (L : X →L[ℝ] ℝ) :
    _root_.Filter.Tendsto (fun n => ∫ x, φ x * L (U n x) ∂μ) l
      (𝓝 (∫ x, φ x * L (u x) ∂μ)) := by
  let B : ℝ →L[ℝ] X →L[ℝ] ℝ := (ContinuousLinearMap.lsmul ℝ ℝ).flip.comp L |>.flip
  have heq (v : _root_.MeasureTheory.Lp X 2 μ) :
      B.lpPairing μ 2 2 (hφ.toLp φ) v = ∫ x, φ x * L (v x) ∂μ := by
    rw [B.lpPairing_eq_integral]
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [hφ.coeFn_toLp] with x hx
    simp only [B, ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.lsmul_apply, hx, smul_eq_mul]
  simpa only [heq] using hU (B.lpPairing μ 2 2 (hφ.toLp φ))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.tendsto_integral_mul_clm_of_weak
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Euclidean.tendsto_integral_mul_clm_of_weak target :: scope.openDecls } }

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "X" => _root_.MeasureTheory.Lp ℝ 2 (volume.restrict Ω)
local notation "Y" => _root_.MeasureTheory.Lp E 2 (volume.restrict Ω)

theorem hasWeakPartialDeriv_of_tendsto_L2_weak_gradient
    {ι : Type*} {l : Filter ι} [_root_.Filter.NeBot l]
    {f : ι → E → ℝ} {v : E → ℝ}
    (hf : ∀ n, DeGiorgi.MemW1pWitness 2 (f n) Ω)
    (hv : _root_.MeasureTheory.MemLp v 2 (volume.restrict Ω)) {G : Y}
    (hlim : _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => f n x - v x) 2
      (volume.restrict Ω)) l (𝓝 0))
    (hG : ∀ z, _root_.Filter.Tendsto (fun n => _root_.Inner.inner ℝ (DeGiorgi.gradLpOfWitness (hf n)) z)
      l (𝓝 (_root_.Inner.inner ℝ G z))) :
    ∀ i, DeGiorgi.HasWeakPartialDeriv i (fun x => G x i) v Ω := by
  have hU : _root_.Filter.Tendsto (fun n => (hf n).memLp.toLp (f n)) l (𝓝 (hv.toLp v)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (f_ℒp := fun n => (hf n).memLp)
      (f_lim_ℒp := hv)).mpr hlim
  have hdual (F : Y →L[ℝ] ℝ) :
      Tendsto (fun n => F (DeGiorgi.gradLpOfWitness (hf n))) l (𝓝 (F G)) := by
    have hF (w : Y) : F w = _root_.Inner.inner ℝ w ((_root_.InnerProductSpace.toDual ℝ Y).symm F) := by
      rw [real_inner_comm, _root_.InnerProductSpace.toDual_symm_apply]
    simpa only [hF] using hG ((_root_.InnerProductSpace.toDual ℝ Y).symm F)
  intro i φ hφ hφc hφs
  have hφm : _root_.MeasureTheory.MemLp φ 2 (volume.restrict Ω) :=
    (hφ.continuous.memLp_of_hasCompactSupport hφc).restrict Ω
  have hdφm : _root_.MeasureTheory.MemLp (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1))
      2 (volume.restrict Ω) :=
    (((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hφc.fderiv_apply ℝ (EuclideanSpace.single i 1))).restrict Ω
  have hleft := tendsto_integral_mul_clm_of_weak
    (fun F : X →L[ℝ] ℝ => (F.continuous.tendsto (hv.toLp v)).comp hU)
    hdφm (ContinuousLinearMap.id ℝ ℝ)
  have hright := (tendsto_integral_mul_clm_of_weak hdual hφm
    (PiLp.proj 2 (fun _ : Fin d => ℝ) i)).neg
  have hfun (n : ι) :
      (∫ x in Ω, fderiv ℝ φ x (EuclideanSpace.single i 1) *
        (hf n).memLp.toLp (f n) x) =
        ∫ x in Ω, f n x * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [(hf n).memLp.coeFn_toLp] with x hx
    rw [hx, mul_comm]
  have hgrad (n : ι) :
      (∫ x in Ω, φ x * (DeGiorgi.gradLpOfWitness (hf n)) x i) =
        ∫ x in Ω, (hf n).weakGrad x i * φ x := by
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [(hf n).weakGrad_memLp.coeFn_toLp] with x hx
    change φ x * (hf n).weakGrad_memLp.toLp (hf n).weakGrad x i = _
    rw [hx, mul_comm]
  have hvfun : (∫ x in Ω, fderiv ℝ φ x (EuclideanSpace.single i 1) * hv.toLp v x) =
      ∫ x in Ω, v x * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [hv.coeFn_toLp] with x hx
    rw [hx, mul_comm]
  simp only [ContinuousLinearMap.id_apply, hfun, hvfun] at hleft
  simp only [PiLp.proj_apply, hgrad] at hright
  have heq : (fun n => ∫ x in Ω, f n x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
      fun n => -∫ x in Ω, (hf n).weakGrad x i * φ x := by
    funext n
    exact (hf n).isWeakGrad i φ hφ hφc hφs
  rw [heq] at hleft
  have h := tendsto_nhds_unique hleft hright
  simpa only [mul_comm] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.hasWeakPartialDeriv_of_tendsto_L2_weak_gradient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.hasWeakPartialDeriv_of_tendsto_L2_weak_gradient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.hasWeakPartialDeriv_of_tendsto_L2_weak_gradient ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.hasWeakPartialDeriv_of_tendsto_L2_weak_gradient

theorem exists_subseq_weak_gradient_of_tendsto_L2
    {f : ℕ → E → ℝ} {v : E → ℝ}
    (hf : ∀ n, DeGiorgi.MemW1pWitness 2 (f n) Ω)
    (hv : _root_.MeasureTheory.MemLp v 2 (volume.restrict Ω)) {C : ℝ}
    (hbound : ∀ n, ‖DeGiorgi.gradLpOfWitness (hf n)‖ ≤ C)
    (hlim : _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => f n x - v x) 2
      (volume.restrict Ω)) _root_.Filter.atTop (𝓝 0)) :
    ∃ (σ : ℕ → ℕ) (G : Y), StrictMono σ ∧ ‖G‖ ≤ C ∧
      (∀ z, _root_.Filter.Tendsto (fun n => _root_.Inner.inner ℝ (DeGiorgi.gradLpOfWitness (hf (σ n))) z)
        _root_.Filter.atTop (𝓝 (_root_.Inner.inner ℝ G z))) ∧
      ∀ i, DeGiorgi.HasWeakPartialDeriv i (fun x => G x i) v Ω := by
  let _ : _root_.MeasureTheory.IsSeparable (volume.restrict Ω) := inferInstance
  let _ : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let _ : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  let _ : SecondCountableTopology Y := Lp.SecondCountableTopology
  let _ : TopologicalSpace.SeparableSpace Y :=
    TopologicalSpace.SecondCountableTopology.to_separableSpace
  let V : ℕ → Y := fun n => DeGiorgi.gradLpOfWitness (hf n)
  obtain ⟨σ, G, hσ, hG⟩ :=
    Analysis.InnerProductSpace.exists_weakly_convergent_subsequence_of_norm_bounded V hbound
  have hGC : ‖G‖ ≤ C := by
    have hvv : _root_.Inner.inner ℝ G G ≤ C * ‖G‖ := le_of_tendsto (hG G) (Eventually.of_forall fun n =>
      (real_inner_le_norm (V (σ n)) G).trans
        (mul_le_mul_of_nonneg_right (hbound (σ n)) (norm_nonneg G)))
    rw [real_inner_self_eq_norm_sq] at hvv
    have hC : 0 ≤ C := (norm_nonneg (V 0)).trans (hbound 0)
    nlinarith [norm_nonneg G]
  exact ⟨σ, G, hσ, hGC, hG, hasWeakPartialDeriv_of_tendsto_L2_weak_gradient
    (fun n => hf (σ n)) hv (hlim.comp hσ.tendsto_atTop) hG⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_subseq_weak_gradient_of_tendsto_L2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_subseq_weak_gradient_of_tendsto_L2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_subseq_weak_gradient_of_tendsto_L2 ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_subseq_weak_gradient_of_tendsto_L2

theorem exists_memW1pWitness_of_tendsto_L2_norm_bounded
    {f : ℕ → E → ℝ} {v : E → ℝ}
    (hf : ∀ n, DeGiorgi.MemW1pWitness 2 (f n) Ω)
    (hv : _root_.MeasureTheory.MemLp v 2 (volume.restrict Ω)) {C : ℝ}
    (hbound : ∀ n, ‖DeGiorgi.gradLpOfWitness (hf n)‖ ≤ C)
    (hlim : _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => f n x - v x) 2
      (volume.restrict Ω)) _root_.Filter.atTop (𝓝 0)) :
    ∃ (σ : ℕ → ℕ) (hw : DeGiorgi.MemW1pWitness 2 v Ω), StrictMono σ ∧
      ‖DeGiorgi.gradLpOfWitness hw‖ ≤ C ∧
      ∀ z : Y, _root_.Filter.Tendsto (fun n => _root_.Inner.inner ℝ (DeGiorgi.gradLpOfWitness (hf (σ n))) z)
        atTop (𝓝 (_root_.Inner.inner ℝ (DeGiorgi.gradLpOfWitness hw) z)) := by
  obtain ⟨σ, G, hσ, hGC, hG, hw⟩ :=
    exists_subseq_weak_gradient_of_tendsto_L2 hf hv hbound hlim
  let hwv : DeGiorgi.MemW1pWitness 2 v Ω :=
    { memLp := hv
      weakGrad := G
      weakGrad_component_memLp := fun i => (Lp.memLp G).eval_piLp i
      isWeakGrad := hw }
  have heq : DeGiorgi.gradLpOfWitness hwv = G := by
    apply Lp.ext
    exact hwv.weakGrad_memLp.coeFn_toLp
  refine ⟨σ, hwv, hσ, ?_, ?_⟩
  · simpa only [heq] using hGC
  · simpa only [heq] using hG

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_memW1pWitness_of_tendsto_L2_norm_bounded then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_memW1pWitness_of_tendsto_L2_norm_bounded"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_memW1pWitness_of_tendsto_L2_norm_bounded ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_memW1pWitness_of_tendsto_L2_norm_bounded

private theorem exists_subseq_weak_gradients_finset_of_tendsto_L2
    {ι : Type*} (s : Finset ι)
    (f : ι → ℕ → E → ℝ) (v : ι → E → ℝ)
    (hf : ∀ i n, DeGiorgi.MemW1pWitness 2 (f i n) Ω)
    (hv : ∀ i, _root_.MeasureTheory.MemLp (v i) 2 (volume.restrict Ω)) (C : ι → ℝ)
    (hbound : ∀ i n, ‖DeGiorgi.gradLpOfWitness (hf i n)‖ ≤ C i)
    (hlim : ∀ i, _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => f i n x - v i x) 2
      (volume.restrict Ω)) _root_.Filter.atTop (𝓝 0)) :
    ∃ (σ : ℕ → ℕ) (G : ι → Y), StrictMono σ ∧ ∀ i ∈ s,
      ‖G i‖ ≤ C i ∧
      (∀ z, _root_.Filter.Tendsto (fun n => _root_.Inner.inner ℝ (DeGiorgi.gradLpOfWitness (hf i (σ n))) z)
        _root_.Filter.atTop (𝓝 (_root_.Inner.inner ℝ (G i) z))) ∧
      ∀ j, DeGiorgi.HasWeakPartialDeriv j (fun x => G i x j) (v i) Ω := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨id, fun _ => 0, strictMono_id, by simp⟩
  | @insert i s _ ih =>
    obtain ⟨σ, G, hσ, hG⟩ := ih
    obtain ⟨τ, A, hτ, hAC, hAlim, hAweak⟩ :=
      exists_subseq_weak_gradient_of_tendsto_L2 (fun n => hf i (σ n)) (hv i)
        (fun n => hbound i (σ n)) ((hlim i).comp hσ.tendsto_atTop)
    refine ⟨σ ∘ τ, Function.update G i A, hσ.comp hτ, ?_⟩
    intro j hj
    by_cases hji : j = i
    · subst j
      rw [Function.update_self]
      exact ⟨hAC, hAlim, hAweak⟩
    · rw [Function.update_of_ne hji]
      obtain ⟨hGC, hGlim, hGweak⟩ := hG j ((Finset.mem_insert.mp hj).resolve_left hji)
      exact ⟨hGC, fun z => (hGlim z).comp hτ.tendsto_atTop, hGweak⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_subseq_weak_gradients_finset_of_tendsto_L2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_subseq_weak_gradients_finset_of_tendsto_L2 target :: scope.openDecls } }

theorem exists_subseq_memW1pWitnesses_of_tendsto_L2_norm_bounded
    {ι : Type*} [Finite ι]
    (f : ι → ℕ → E → ℝ) (v : ι → E → ℝ)
    (hf : ∀ i n, DeGiorgi.MemW1pWitness 2 (f i n) Ω)
    (hv : ∀ i, _root_.MeasureTheory.MemLp (v i) 2 (volume.restrict Ω)) (C : ι → ℝ)
    (hbound : ∀ i n, ‖DeGiorgi.gradLpOfWitness (hf i n)‖ ≤ C i)
    (hlim : ∀ i, _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => f i n x - v i x) 2
      (volume.restrict Ω)) _root_.Filter.atTop (𝓝 0)) :
    ∃ (σ : ℕ → ℕ) (hw : ∀ i, DeGiorgi.MemW1pWitness 2 (v i) Ω), StrictMono σ ∧
      (∀ i, ‖DeGiorgi.gradLpOfWitness (hw i)‖ ≤ C i) ∧
      ∀ i (z : Y), _root_.Filter.Tendsto (fun n => _root_.Inner.inner ℝ (DeGiorgi.gradLpOfWitness (hf i (σ n))) z)
        atTop (𝓝 (_root_.Inner.inner ℝ (DeGiorgi.gradLpOfWitness (hw i)) z)) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  obtain ⟨σ, G, hσ, hG⟩ := exists_subseq_weak_gradients_finset_of_tendsto_L2
    Finset.univ f v hf hv C hbound hlim
  let hw : ∀ i, DeGiorgi.MemW1pWitness 2 (v i) Ω := fun i =>
    { memLp := hv i
      weakGrad := G i
      weakGrad_component_memLp := fun j => (Lp.memLp (G i)).eval_piLp j
      isWeakGrad := (hG i (Finset.mem_univ i)).2.2 }
  have heq (i : ι) : DeGiorgi.gradLpOfWitness (hw i) = G i := by
    apply Lp.ext
    exact (hw i).weakGrad_memLp.coeFn_toLp
  refine ⟨σ, hw, hσ, ?_, ?_⟩
  · intro i
    simpa only [heq] using (hG i (Finset.mem_univ i)).1
  · intro i
    simpa only [heq] using (hG i (Finset.mem_univ i)).2.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_subseq_memW1pWitnesses_of_tendsto_L2_norm_bounded then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_subseq_memW1pWitnesses_of_tendsto_L2_norm_bounded"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_subseq_memW1pWitnesses_of_tendsto_L2_norm_bounded ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_subseq_memW1pWitnesses_of_tendsto_L2_norm_bounded

end DifferentialGeometry.Analysis.Sobolev.Euclidean
