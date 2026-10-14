import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornArmSubsequence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set
open scoped _root_.Topology _root_.Submission.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W] [SigmaCompactSpace W]

theorem finiteHorn_two_arm_subsequence_eq_endRay
    (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g) :
    ∃ d : ℝ, 0 < d ∧ ∀ (a : Fin 2 → EndRay H.endpoint) (r : Fin 2 → ℝ),
      (∀ k, 0 < r k) → (∀ k, r k < _root_.Min.min (a k).length d) → ∀ i : ℕ,
      ∀ (length : Fin 2 → ℕ → ℝ) (c : Fin 2 → ℕ → _root_.Set.Icc (0 : ℝ) 1 → W),
        (∀ k n, 0 ≤ length k n) → (∀ k, _root_.Filter.Tendsto (length k) _root_.Filter.atTop (𝓝 (r k))) →
        (∀ k n s, c k n s ∈ H.subend i) →
        (∀ k n s t, _root_.Dist.dist (c k n s) (c k n t) = length k n * _root_.Dist.dist s t) →
        (∀ k, _root_.Filter.Tendsto (fun n => (c k n ⟨0, by norm_num⟩ : UniformSpace.Completion W))
          _root_.Filter.atTop (𝓝 H.endpoint)) →
        (∀ k n, c k n ⟨1, by norm_num⟩ = (a k).point (r k)) →
        ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∀ k,
          TendstoUniformly (fun n s => (c k (phi n) s : UniformSpace.Completion W))
            (fun s : _root_.Set.Icc (0 : ℝ) 1 => if (s : ℝ) = 0 then H.endpoint
              else ((a k).point (r k * s) : UniformSpace.Completion W)) atTop := by
  obtain ⟨d, hd, hsub⟩ := finiteHorn_arm_subsequence_eq_endRay g H
  refine ⟨d, hd, ?_⟩
  intro a r hr hrd i length c hlength hlengthT hmem hdist hbase hend
  obtain ⟨phi, hphi, hfirst⟩ := hsub (a 0) (r 0) (hr 0) (hrd 0) i
    (length 0) (c 0) (hlength 0) (hlengthT 0) (hmem 0) (hdist 0) (hbase 0) (hend 0)
  obtain ⟨psi, hpsi, hsecond⟩ := hsub (a 1) (r 1) (hr 1) (hrd 1) i
    (fun n => length 1 (phi n)) (fun n s => c 1 (phi n) s)
    (fun n => hlength 1 (phi n)) ((hlengthT 1).comp hphi.tendsto_atTop)
    (fun n s => hmem 1 (phi n) s) (fun n s t => hdist 1 (phi n) s t)
    ((hbase 1).comp hphi.tendsto_atTop) (fun n => hend 1 (phi n))
  refine ⟨phi ∘ psi, hphi.comp hpsi, ?_⟩
  intro k
  fin_cases k
  · exact (tendstoUniformly_iff_seq_tendstoUniformly.mp hfirst) psi hpsi.tendsto_atTop
  · exact hsecond

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_two_arm_subsequence_eq_endRay then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_two_arm_subsequence_eq_endRay"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_two_arm_subsequence_eq_endRay ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_two_arm_subsequence_eq_endRay

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
