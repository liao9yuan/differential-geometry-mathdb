import Submission.DifferentialGeometry.Topology.MetricSpace.GeodesicCompactness
import Mathlib.Topology.Order.LiminfLimsup

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Filter _root_.Set _root_.BoundedContinuousFunction
open scoped _root_.Topology _root_.NNReal _root_.BoundedContinuousFunction.NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

variable {X : Type*} [MetricSpace X]

theorem exists_uniform_limit_of_compact_metric_segments
    {K : Set X} (hK : IsCompact K) {length : ℕ → ℝ} {r : ℝ}
    (hlength : ∀ n, 0 ≤ length n) (hlengthT : _root_.Filter.Tendsto length _root_.Filter.atTop (𝓝 r))
    (c : ℕ → _root_.Set.Icc (0 : ℝ) 1 → X)
    (hmem : ∀ n s, c n s ∈ K)
    (hdist : ∀ n s t, _root_.Dist.dist (c n s) (c n t) = length n * _root_.Dist.dist s t)
    {p q : X}
    (hp : _root_.Filter.Tendsto (fun n => c n ⟨0, by norm_num⟩) _root_.Filter.atTop (𝓝 p))
    (hq : _root_.Filter.Tendsto (fun n => c n ⟨1, by norm_num⟩) _root_.Filter.atTop (𝓝 q)) :
    ∃ (f : _root_.Set.Icc (0 : ℝ) 1 → X) (phi : ℕ → ℕ),
      StrictMono phi ∧ Continuous f ∧ TendstoUniformly (fun n => c (phi n)) f _root_.Filter.atTop ∧
      f ⟨0, by norm_num⟩ = p ∧ f ⟨1, by norm_num⟩ = q ∧
      (∀ s, f s ∈ K) ∧ ∀ s t, _root_.Dist.dist (f s) (f t) = r * _root_.Dist.dist s t := by
  obtain ⟨B, hB⟩ := hlengthT.bddAbove_range
  have hBnonneg : 0 ≤ B := (hlength 0).trans (hB (_root_.Set.mem_range_self 0))
  let L : ℝ≥0 := ⟨B, hBnonneg⟩
  have hLip (n : ℕ) : LipschitzWith L (c n) := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    rw [hdist n s t]
    exact mul_le_mul_of_nonneg_right (hB (_root_.Set.mem_range_self n)) dist_nonneg
  let T := _root_.Set.Icc (0 : ℝ) 1
  let F (n : ℕ) : T →ᵇ X :=
    BoundedContinuousFunction.mkOfCompact ⟨c n, (hLip n).continuous⟩
  let A := _root_.Set.range F
  have hEA : Equicontinuous (fun f : A => ((f : T →ᵇ X) : T → X)) := by
    apply UniformEquicontinuous.equicontinuous
    apply LipschitzWith.uniformEquicontinuous _ L
    intro f
    obtain ⟨n, hn⟩ := f.property
    rw [← hn]
    exact hLip n
  have hAcpt : IsCompact (closure A) := by
    apply BoundedContinuousFunction.arzela_ascoli K hK A
    · intro f s hf
      obtain ⟨n, rfl⟩ := hf
      exact hmem n s
    · exact hEA
  obtain ⟨f, _hf, phi, hphi, hlim⟩ :=
    hAcpt.tendsto_subseq (fun n => subset_closure (_root_.Set.mem_range_self n))
  have heval (s : T) : _root_.Filter.Tendsto (fun n => c (phi n) s) _root_.Filter.atTop (𝓝 (f s)) :=
    ((BoundedContinuousFunction.lipschitz_eval_const s).continuous.tendsto f).comp hlim
  have huniform : TendstoUniformly (fun n => c (phi n)) f atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hlim
  have hzero : f ⟨0, by norm_num [T]⟩ = p :=
    tendsto_nhds_unique (heval ⟨0, by norm_num [T]⟩) (hp.comp hphi.tendsto_atTop)
  have hone : f ⟨1, by norm_num [T]⟩ = q :=
    tendsto_nhds_unique (heval ⟨1, by norm_num [T]⟩) (hq.comp hphi.tendsto_atTop)
  refine ⟨f, phi, hphi, f.continuous, huniform, hzero, hone, ?_, ?_⟩
  · intro s
    exact hK.isClosed.mem_of_tendsto (heval s)
      (Eventually.of_forall (fun n => hmem (phi n) s))
  · intro s t
    have hpair := (heval s).dist (heval t)
    have hscale := (hlengthT.comp hphi.tendsto_atTop).mul_const (_root_.Dist.dist s t)
    exact tendsto_nhds_unique hpair
      (hscale.congr (fun n => (hdist (phi n) s t).symm))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.exists_uniform_limit_of_compact_metric_segments then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.exists_uniform_limit_of_compact_metric_segments"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.exists_uniform_limit_of_compact_metric_segments ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.exists_uniform_limit_of_compact_metric_segments

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
