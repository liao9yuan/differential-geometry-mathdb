import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.ZeroBoundaryGraph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Filter _root_.Set
open scoped _root_.ENNReal _root_.Topology

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} [NeZero d] {Ω : Set (EuclideanSpace ℝ (Fin d))}

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "Y" => _root_.MeasureTheory.Lp E 2 (volume.restrict Ω)

omit [NeZero d] in
private theorem gradLpOfWitness_eq_of_hasWeakPartialDeriv (hΩ : IsOpen Ω)
    {v : E → ℝ} (hv : DeGiorgi.MemW1pWitness 2 v Ω) {G : Y}
    (hG : ∀ i, DeGiorgi.HasWeakPartialDeriv i (fun x => G x i) v Ω) :
    G = DeGiorgi.gradLpOfWitness hv := by
  have hcoord (i : Fin d) : (fun x => G x i) =ᵐ[volume.restrict Ω]
      (fun x => hv.weakGrad x i) :=
    DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ (hG i) (hv.isWeakGrad i)
      (((Lp.memLp G).eval_piLp i).locallyIntegrable (by norm_num))
      ((hv.weakGrad_component_memLp i).locallyIntegrable (by norm_num))
  apply Lp.ext
  filter_upwards [ae_all_iff.mpr hcoord, hv.weakGrad_memLp.coeFn_toLp] with x hx hg
  change G x = hv.weakGrad_memLp.toLp hv.weakGrad x
  rw [hg]
  exact PiLp.ext hx

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.gradLpOfWitness_eq_of_hasWeakPartialDeriv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Euclidean.gradLpOfWitness_eq_of_hasWeakPartialDeriv target :: scope.openDecls } }

private theorem exists_subseq_tendsto_inner_gradient (hΩ : IsOpen Ω)
    {f : ℕ → E → ℝ} {v : E → ℝ}
    (hf : ∀ n, DeGiorgi.MemW01p 2 (f n) Ω)
    (hv : DeGiorgi.MemW1pWitness 2 v Ω) {C : ℝ}
    (hbound : ∀ n, ‖DeGiorgi.gradLpOfWitness (Classical.choose (hf n).2)‖ ≤ C)
    (hlim : _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => f n x - v x) 2
      (volume.restrict Ω)) _root_.Filter.atTop (𝓝 0)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ z : Y,
      _root_.Filter.Tendsto (fun n => _root_.Inner.inner ℝ (DeGiorgi.gradLpOfWitness
        (Classical.choose (hf (σ n)).2)) z) _root_.Filter.atTop
        (𝓝 (_root_.Inner.inner ℝ (DeGiorgi.gradLpOfWitness hv) z)) := by
  obtain ⟨_, σ, G, hσ, _, hw, hG⟩ :=
    exists_weakly_convergent_gradients_of_tendsto_L2 hΩ hf hv.memLp hbound hlim
  rw [gradLpOfWitness_eq_of_hasWeakPartialDeriv hΩ hv hG] at hw
  exact ⟨σ, hσ, hw⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_subseq_tendsto_inner_gradient
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_subseq_tendsto_inner_gradient target :: scope.openDecls } }

private theorem exists_subseq_tendsto_inner_gradients_finset
    {ι : Type*} (s : Finset ι) (hΩ : IsOpen Ω)
    (f : ι → ℕ → E → ℝ) (v : ι → E → ℝ)
    (hf : ∀ i n, DeGiorgi.MemW01p 2 (f i n) Ω)
    (hv : ∀ i, DeGiorgi.MemW1pWitness 2 (v i) Ω) (C : ι → ℝ)
    (hbound : ∀ i n, ‖DeGiorgi.gradLpOfWitness (Classical.choose (hf i n).2)‖ ≤ C i)
    (hlim : ∀ i, _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => f i n x - v i x) 2
      (volume.restrict Ω)) _root_.Filter.atTop (𝓝 0)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ i ∈ s, ∀ z : Y,
      _root_.Filter.Tendsto (fun n => _root_.Inner.inner ℝ (DeGiorgi.gradLpOfWitness
        (Classical.choose (hf i (σ n)).2)) z) _root_.Filter.atTop
        (𝓝 (_root_.Inner.inner ℝ (DeGiorgi.gradLpOfWitness (hv i)) z)) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨id, strictMono_id, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨σ, hσ, hσlim⟩ := ih
    obtain ⟨τ, hτ, hτlim⟩ := exists_subseq_tendsto_inner_gradient hΩ
      (fun n => hf i (σ n)) (hv i) (fun n => hbound i (σ n))
      ((hlim i).comp hσ.tendsto_atTop)
    refine ⟨σ ∘ τ, hσ.comp hτ, ?_⟩
    intro j hj z
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hτlim z
    · exact (hσlim j hj z).comp hτ.tendsto_atTop

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_subseq_tendsto_inner_gradients_finset
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_subseq_tendsto_inner_gradients_finset target :: scope.openDecls } }

theorem exists_subseq_tendsto_inner_gradients
    {ι : Type*} [Finite ι] (hΩ : IsOpen Ω)
    (f : ι → ℕ → E → ℝ) (v : ι → E → ℝ)
    (hf : ∀ i n, DeGiorgi.MemW01p 2 (f i n) Ω)
    (hv : ∀ i, DeGiorgi.MemW1pWitness 2 (v i) Ω) (C : ι → ℝ)
    (hbound : ∀ i n, ‖DeGiorgi.gradLpOfWitness (Classical.choose (hf i n).2)‖ ≤ C i)
    (hlim : ∀ i, _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => f i n x - v i x) 2
      (volume.restrict Ω)) _root_.Filter.atTop (𝓝 0)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ i, ∀ z : Y,
      _root_.Filter.Tendsto (fun n => _root_.Inner.inner ℝ (DeGiorgi.gradLpOfWitness
        (Classical.choose (hf i (σ n)).2)) z) _root_.Filter.atTop
        (𝓝 (_root_.Inner.inner ℝ (DeGiorgi.gradLpOfWitness (hv i)) z)) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  obtain ⟨σ, hσ, hlim⟩ := exists_subseq_tendsto_inner_gradients_finset Finset.univ
    hΩ f v hf hv C hbound hlim
  exact ⟨σ, hσ, fun i => hlim i (Finset.mem_univ i)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_subseq_tendsto_inner_gradients then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_subseq_tendsto_inner_gradients"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_subseq_tendsto_inner_gradients ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_subseq_tendsto_inner_gradients

end DifferentialGeometry.Analysis.Sobolev.Euclidean
