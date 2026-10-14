import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Sequences

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Filter _root_.Set _root_.BoundedContinuousFunction
open scoped _root_.Topology _root_.NNReal _root_.BoundedContinuousFunction.NNReal

namespace Metric

variable {X : Type*} [MetricSpace X]

theorem dist_eq_mul_of_lipschitz_interval {L : ℝ≥0}
    (f : _root_.Set.Icc (0 : ℝ) 1 → X) (hf : LipschitzWith L f)
    (hend : _root_.Dist.dist (f ⟨0, by norm_num⟩) (f ⟨1, by norm_num⟩) = L) :
    ∀ s t, _root_.Dist.dist (f s) (f t) = (L : ℝ) * _root_.Dist.dist s t := by
  have hordered (s t : _root_.Set.Icc (0 : ℝ) 1) (hst : (s : ℝ) ≤ t) :
      dist (f s) (f t) = (L : ℝ) * _root_.Dist.dist s t := by
    let z : _root_.Set.Icc (0 : ℝ) 1 := ⟨0, by norm_num⟩
    let o : _root_.Set.Icc (0 : ℝ) 1 := ⟨1, by norm_num⟩
    have hzs := hf.dist_le_mul z s
    have hto := hf.dist_le_mul t o
    have hst' := hf.dist_le_mul s t
    change _root_.Dist.dist (f z) (f s) ≤ (L : ℝ) * |0 - (s : ℝ)| at hzs
    change _root_.Dist.dist (f t) (f o) ≤ (L : ℝ) * |(t : ℝ) - 1| at hto
    change _root_.Dist.dist (f s) (f t) ≤ (L : ℝ) * |(s : ℝ) - (t : ℝ)| at hst'
    rw [zero_sub, abs_neg, abs_of_nonneg s.property.1] at hzs
    rw [abs_of_nonpos (sub_nonpos.mpr t.property.2)] at hto
    rw [abs_of_nonpos (sub_nonpos.mpr hst)] at hst'
    have htri₁ := dist_triangle (f z) (f s) (f o)
    have htri₂ := dist_triangle (f s) (f t) (f o)
    have hfull : _root_.Dist.dist (f z) (f o) = L := hend
    rw [hfull] at htri₁
    change _root_.Dist.dist (f s) (f t) = (L : ℝ) * |(s : ℝ) - (t : ℝ)|
    rw [abs_of_nonpos (sub_nonpos.mpr hst)]
    linarith
  intro s t
  rcases le_total (s : ℝ) (t : ℝ) with hst | hts
  · exact hordered s t hst
  · calc
      _ = _root_.Dist.dist (f t) (f s) := dist_comm _ _
      _ = (L : ℝ) * _root_.Dist.dist t s := hordered t s hts
      _ = _ := by rw [dist_comm t s]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Metric.dist_eq_mul_of_lipschitz_interval then
    throwError "Refusing to shadow existing declaration Metric.dist_eq_mul_of_lipschitz_interval"
  Lean.modifyEnv fun env => Lean.addAlias env `Metric.dist_eq_mul_of_lipschitz_interval ``Submission.Metric.dist_eq_mul_of_lipschitz_interval

theorem exists_metric_segment_of_compact_lipschitz_curves
    {K : Set X} (hK : IsCompact K) {L : ℝ≥0} {p q : X} (hpq : _root_.Dist.dist p q = L)
    (c : ℕ → ℝ → X)
    (hc : ∀ n, ContinuousOn (c n) (_root_.Set.Icc (0 : ℝ) 1))
    (hmem : ∀ n, ∀ s ∈ _root_.Set.Icc (0 : ℝ) 1, c n s ∈ K)
    (hLip : ∀ n, LipschitzOnWith L (c n) (_root_.Set.Icc (0 : ℝ) 1))
    (hp : _root_.Filter.Tendsto (fun n => c n 0) _root_.Filter.atTop (𝓝 p))
    (hq : _root_.Filter.Tendsto (fun n => c n 1) _root_.Filter.atTop (𝓝 q)) :
    ∃ f : _root_.Set.Icc (0 : ℝ) 1 → X, Continuous f ∧
      f ⟨0, by norm_num⟩ = p ∧ f ⟨1, by norm_num⟩ = q ∧
      (∀ s, f s ∈ K) ∧ ∀ s t, _root_.Dist.dist (f s) (f t) = (L : ℝ) * _root_.Dist.dist s t := by
  let T := _root_.Set.Icc (0 : ℝ) 1
  let F (n : ℕ) : T →ᵇ X :=
    BoundedContinuousFunction.mkOfCompact ⟨fun s => c n s, (hc n).domRestrict⟩
  have hLF (n : ℕ) : LipschitzWith L (F n) := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    exact (lipschitzOnWith_iff_dist_le_mul.mp (hLip n)) a a.property b b.property
  let A := _root_.Set.range F
  have hEA : Equicontinuous (fun f : A => ((f : T →ᵇ X) : T → X)) := by
    apply UniformEquicontinuous.equicontinuous
    apply LipschitzWith.uniformEquicontinuous _ L
    intro f
    obtain ⟨n, hn⟩ := f.property
    rw [← hn]
    exact hLF n
  have hAcpt : IsCompact (closure A) := by
    apply BoundedContinuousFunction.arzela_ascoli K hK A
    · intro f s hf
      obtain ⟨n, rfl⟩ := hf
      exact hmem n s s.property
    · exact hEA
  obtain ⟨f, _hf, phi, hphi, hlim⟩ :=
    hAcpt.tendsto_subseq (fun n => subset_closure (_root_.Set.mem_range_self n))
  have heval (s : T) : _root_.Filter.Tendsto (fun n => F (phi n) s) _root_.Filter.atTop (𝓝 (f s)) :=
    ((BoundedContinuousFunction.lipschitz_eval_const s).continuous.tendsto f).comp hlim
  have hfl : LipschitzWith L f := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    exact le_of_tendsto ((heval a).dist (heval b))
      (Eventually.of_forall (fun n => (hLF (phi n)).dist_le_mul a b))
  have hzero : f ⟨0, by norm_num [T]⟩ = p :=
    tendsto_nhds_unique (heval ⟨0, by norm_num [T]⟩) (hp.comp hphi.tendsto_atTop)
  have hone : f ⟨1, by norm_num [T]⟩ = q :=
    tendsto_nhds_unique (heval ⟨1, by norm_num [T]⟩) (hq.comp hphi.tendsto_atTop)
  refine ⟨f, f.continuous, hzero, hone, ?_, ?_⟩
  · intro s
    exact hK.isClosed.mem_of_tendsto (heval s)
      (Eventually.of_forall (fun n => hmem (phi n) s s.property))
  · apply dist_eq_mul_of_lipschitz_interval f hfl
    rw [hzero, hone]
    exact hpq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Metric.exists_metric_segment_of_compact_lipschitz_curves then
    throwError "Refusing to shadow existing declaration Metric.exists_metric_segment_of_compact_lipschitz_curves"
  Lean.modifyEnv fun env => Lean.addAlias env `Metric.exists_metric_segment_of_compact_lipschitz_curves ``Submission.Metric.exists_metric_segment_of_compact_lipschitz_curves

end Metric
