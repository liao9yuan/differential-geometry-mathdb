import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.LipschitzWitness
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.Rellich.UnitBall
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.WeakLimit

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.NNReal _root_.ENNReal _root_.Topology

namespace DifferentialGeometry.Analysis.Sobolev

variable {d : ℕ} [NeZero d] {ι : Type*} [Fintype ι]

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ ι

theorem exists_tendsto_L2_subseq_of_lipschitz_of_energy_bound
    (f : ℕ → E → F) (K : ℕ → ℝ≥0)
    (hf : ∀ n, LipschitzWith (K n) (f n))
    {D B : ℝ} (hD : ∀ n, ∀ᵐ x ∂volume.restrict (Metric.ball 0 1), ‖f n x‖ ≤ D)
    (hB : ∀ n, (∫ x in Metric.ball 0 1, ‖fderiv ℝ (f n) x‖ ^ 2) ≤ B)
    {S : Set F} (hS : IsClosed S)
    (himage : ∀ n, ∀ᵐ x ∂volume.restrict (Metric.ball 0 1), f n x ∈ S) :
    ∃ (φ : ℕ → ℕ) (v : E → F),
      StrictMono φ ∧ _root_.MeasureTheory.MemLp v 2 (volume.restrict (Metric.ball 0 1)) ∧
      _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => f (φ n) x - v x) 2
        (volume.restrict (Metric.ball 0 1))) _root_.Filter.atTop (𝓝 0) ∧
      (∀ᵐ x ∂volume.restrict (Metric.ball 0 1),
        _root_.Filter.Tendsto (fun n => f (φ n) x) _root_.Filter.atTop (𝓝 (v x))) ∧
      ∀ᵐ x ∂volume.restrict (Metric.ball 0 1), v x ∈ S := by
  let : _root_.MeasureTheory.IsFiniteMeasure (volume.restrict (Metric.ball (0 : E) 1)) :=
    isFiniteMeasure_restrict.mpr ((_root_.MeasureTheory.measure_mono Metric.ball_subset_closedBall).trans_lt
      (_root_.ProperSpace.isCompact_closedBall (0 : E) 1).measure_lt_top).ne
  obtain ⟨R, hw, _, hfun, hgrad⟩ :=
    Euclidean.exists_uniform_coordinate_memW1pWitness_of_lipschitz f K hf hD hB
  exact rellich_kondrachov_W12_seq_unitBall_euclidean_closed_image f
    (fun i n => hw n i) (fun _ => R) (fun i n => hfun n i) (fun i n => hgrad n i)
    hS himage

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.exists_tendsto_L2_subseq_of_lipschitz_of_energy_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.exists_tendsto_L2_subseq_of_lipschitz_of_energy_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.exists_tendsto_L2_subseq_of_lipschitz_of_energy_bound ``Submission.DifferentialGeometry.Analysis.Sobolev.exists_tendsto_L2_subseq_of_lipschitz_of_energy_bound

end DifferentialGeometry.Analysis.Sobolev

end

noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.NNReal _root_.ENNReal _root_.Topology

namespace DifferentialGeometry.Analysis.Sobolev

variable {d : ℕ} [NeZero d] {ι : Type*} [Fintype ι]

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ ι
local notation "μ" => volume.restrict (Metric.ball (0 : E) 1)

theorem exists_weak_memW1p_subseq_of_lipschitz_of_energy_bound
    (f : ℕ → E → F) (K : ℕ → ℝ≥0)
    (hf : ∀ n, LipschitzWith (K n) (f n))
    {D B : ℝ} (hD : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ D)
    (hB : ∀ n, (∫ x in Metric.ball 0 1, ‖fderiv ℝ (f n) x‖ ^ 2) ≤ B)
    {S : Set F} (hS : IsClosed S)
    (himage : ∀ n, ∀ᵐ x ∂μ, f n x ∈ S) :
    ∃ (hs : ∀ n i, DeGiorgi.MemW1pWitness 2 (fun x => f n x i) (Metric.ball 0 1))
      (φ : ℕ → ℕ) (v : E → F)
      (hv : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => v x i) (Metric.ball 0 1)),
      StrictMono φ ∧
      (∀ n i x j, (hs n i).weakGrad x j =
        fderiv ℝ (fun y => f n y i) x (EuclideanSpace.single j 1)) ∧
      _root_.MeasureTheory.MemLp v 2 μ ∧
      _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => f (φ n) x - v x) 2 μ) _root_.Filter.atTop (𝓝 0) ∧
      (∀ᵐ x ∂μ, _root_.Filter.Tendsto (fun n => f (φ n) x) _root_.Filter.atTop (𝓝 (v x))) ∧
      (∀ᵐ x ∂μ, v x ∈ S) ∧
      ∀ i (z : _root_.MeasureTheory.Lp E 2 μ),
        _root_.Filter.Tendsto (fun n => _root_.Inner.inner ℝ (DeGiorgi.gradLpOfWitness (hs (φ n) i)) z) _root_.Filter.atTop
          (𝓝 (_root_.Inner.inner ℝ (DeGiorgi.gradLpOfWitness (hv i)) z)) := by
  let : _root_.MeasureTheory.IsFiniteMeasure μ :=
    isFiniteMeasure_restrict.mpr ((_root_.MeasureTheory.measure_mono Metric.ball_subset_closedBall).trans_lt
      (_root_.ProperSpace.isCompact_closedBall (0 : E) 1).measure_lt_top).ne
  obtain ⟨R, hw, hrep, hfun, hgrad⟩ :=
    Euclidean.exists_uniform_coordinate_memW1pWitness_of_lipschitz f K hf hD hB
  obtain ⟨φ, v, hφ, hv, hlim, hae, hvS⟩ :=
    rellich_kondrachov_W12_seq_unitBall_euclidean_closed_image f
      (fun i n => hw n i) (fun _ => R) (fun i n => hfun n i) (fun i n => hgrad n i)
      hS himage
  have hnorm (i : ι) (n : ℕ) : ‖DeGiorgi.gradLpOfWitness (hw (φ n) i)‖ ≤ _root_.Max.max R 0 := by
    rw [DeGiorgi.gradLpOfWitness, Lp.norm_toLp]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hgrad (φ n) i)).trans_eq
      ENNReal.toReal_ofReal'
  have hcoord (i : ι) : _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => f (φ n) x i - v x i) 2 μ)
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
    intro n
    exact _root_.MeasureTheory.eLpNorm_mono_ae (Filter.Eventually.of_forall fun x =>
      PiLp.norm_apply_le (f (φ n) x - v x) i)
  obtain ⟨ψ, hwv, hψ, _, hweak⟩ :=
    Euclidean.exists_subseq_memW1pWitnesses_of_tendsto_L2_norm_bounded
      (fun i n x => f (φ n) x i) (fun i x => v x i) (fun i n => hw (φ n) i)
      (fun i => hv.eval_piLp i) (fun _ => _root_.Max.max R 0) hnorm hcoord
  refine ⟨hw, φ ∘ ψ, v, hwv, hφ.comp hψ, hrep, hv, hlim.comp hψ.tendsto_atTop,
    ?_, hvS, hweak⟩
  filter_upwards [hae] with x hx
  exact hx.comp hψ.tendsto_atTop

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.exists_weak_memW1p_subseq_of_lipschitz_of_energy_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.exists_weak_memW1p_subseq_of_lipschitz_of_energy_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.exists_weak_memW1p_subseq_of_lipschitz_of_energy_bound ``Submission.DifferentialGeometry.Analysis.Sobolev.exists_weak_memW1p_subseq_of_lipschitz_of_energy_bound

end DifferentialGeometry.Analysis.Sobolev

end
