import Submission.DifferentialGeometry.Topology.Compactness.CountableSubsequence
import Submission.DifferentialGeometry.Analysis.Integration.Measure.CountableAEConvergence
import Mathlib.MeasureTheory.Function.LpSpace.Complete

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

open _root_.Filter
open scoped _root_.ENNReal _root_.Topology

namespace MeasureTheory
open _root_.MeasureTheory

open _root_.MeasureTheory in
theorem exists_seq_tendsto_ae_of_countable_Lp_subseq
    {A I : Type*} {E : I → Type*} [MeasurableSpace A] [Countable I]
    [∀ i, NormedAddCommGroup (E i)] {μ : _root_.MeasureTheory.Measure A} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (f : ℕ → ∀ i, A → E i)
    (hf : ∀ n i, _root_.MeasureTheory.MemLp (f n i) p μ)
    (hcompact : ∀ i (σ : ℕ → ℕ), StrictMono σ →
      ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∃ g : A → E i, _root_.MeasureTheory.MemLp g p μ ∧
        _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (f (σ (τ n)) i - g) p μ) _root_.Filter.atTop (𝓝 0)) :
    ∃ (φ : ℕ → ℕ) (g : ∀ i, A → E i), StrictMono φ ∧
      (∀ i, _root_.MeasureTheory.MemLp (g i) p μ) ∧
      ∀ᵐ z ∂μ, ∀ i, _root_.Filter.Tendsto (fun n => f (φ n) i z) _root_.Filter.atTop (𝓝 (g i z)) := by
  classical
  let _ : Fact (1 ≤ p) := ⟨hp⟩
  let F : ℕ → ∀ i, _root_.MeasureTheory.Lp (E i) p μ := fun n i => (hf n i).toLp (f n i)
  have hF : ∀ i (σ : ℕ → ℕ), StrictMono σ →
      ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∃ v : _root_.MeasureTheory.Lp (E i) p μ,
        Tendsto (fun n => F (σ (τ n)) i) _root_.Filter.atTop (𝓝 v) := by
    intro i σ hσ
    obtain ⟨τ, hτ, g, hg, hlim⟩ := hcompact i σ hσ
    refine ⟨τ, hτ, hg.toLp g, ?_⟩
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun n => f (σ (τ n)) i) (fun n => hf (σ (τ n)) i) g hg).mpr hlim
  obtain ⟨φ, hφ, hlim⟩ := exists_subseq_tendsto_of_countable_coordinatewise_subseq F hF
  choose v hv using hlim
  let g : ∀ i, A → E i := fun i => v i
  have hraw : ∀ i, _root_.MeasureTheory.TendstoInMeasure μ (fun n => f (φ n) i) _root_.Filter.atTop (g i) := by
    intro i
    exact TendstoInMeasure.congr
      (fun n => (hf (φ n) i).coeFn_toLp) Filter.EventuallyEq.rfl
      (_root_.MeasureTheory.tendstoInMeasure_of_tendsto_Lp (hv i))
  obtain ⟨ψ, hψ, hae⟩ := exists_seq_tendsto_ae_of_countable_tendstoInMeasure hraw
  refine ⟨φ ∘ ψ, g, hφ.comp hψ, fun i => Lp.memLp (v i), ?_⟩
  exact hae

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.exists_seq_tendsto_ae_of_countable_Lp_subseq then
    throwError "Refusing to shadow existing declaration MeasureTheory.exists_seq_tendsto_ae_of_countable_Lp_subseq"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.exists_seq_tendsto_ae_of_countable_Lp_subseq ``Submission.MeasureTheory.exists_seq_tendsto_ae_of_countable_Lp_subseq

end MeasureTheory

end
