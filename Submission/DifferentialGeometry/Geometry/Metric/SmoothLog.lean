import Submission.DifferentialGeometry.Geometry.Metric.MinimizingLog
import Submission.DifferentialGeometry.Topology.Compactness.DiagonalNeighborhood

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential
open scoped _root_.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M] [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (TangentSpace I : M → Type _)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]



theorem exists_smooth_minimizingDiagLog_neighborhood (g : SmoothRiemannianMetric I M)
    (hg : IsMetricNorm (I := I) (M := M) g) :
    ∃ U : Set (M × M), IsOpen U ∧ (∀ p : M, (p, p) ∈ U) ∧
      ContMDiffOn (I.prod I) I.tangent ∞ (minimizingDiagLog g hg) U := by
  have hlocal (p : M) : ∃ V : Set (M × M), IsOpen V ∧ (p, p) ∈ V ∧
      ContMDiffOn (I.prod I) I.tangent ∞ (minimizingDiagLog g hg) V := by
    let B := standardDiagonalInverseBranch (I := I) g hg p
    have hB0 : B.hom (TotalSpace.mk' E p 0) = (p, p) := by
      refine (B.hom_eq B.zero_mem).trans ?_
      change (p, expMapIntrinsic (I := I) g hg p 0) = (p, p)
      rw [expMapIntrinsic_zero]
    have hpB : (p, p) ∈ B.hom.target := hB0 ▸ B.hom.map_source B.zero_mem
    obtain ⟨V, hV, hVopen, hpV⟩ := mem_nhds_iff.mp
      (_root_.Filter.inter_mem (B.hom.open_target.mem_nhds hpB)
        (minimizingDiagLog_eventually_eq_branch g hg p))
    refine ⟨V, hVopen, hpV, ?_⟩
    apply (B.inv_contMDiffOn.mono (fun y hy => (hV hy).1)).congr
    intro y hy
    exact (hV hy).2
  choose V hV hpV hsV using hlocal
  refine ⟨⋃ p, V p, isOpen_iUnion hV, fun p => mem_iUnion.mpr ⟨p, hpV p⟩, ?_⟩
  intro y hy
  obtain ⟨p, hyp⟩ := mem_iUnion.mp hy
  exact ((hsV p y hyp).contMDiffAt ((hV p).mem_nhds hyp)).contMDiffWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_smooth_minimizingDiagLog_neighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_smooth_minimizingDiagLog_neighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_smooth_minimizingDiagLog_neighborhood ``Submission.DifferentialGeometry.Geometry.exists_smooth_minimizingDiagLog_neighborhood



theorem exists_uniform_smooth_minimizingDiagLog (g : SmoothRiemannianMetric I M)
    (hg : IsMetricNorm (I := I) (M := M) g) :
    ∃ (ρ : ℝ≥0) (U : Set (M × M)), 0 < ρ ∧ IsOpen U ∧
      (∀ x y, Manifold.riemannianEDist I x y ≤ (ρ : ℝ≥0∞) → (x, y) ∈ U) ∧
      ContMDiffOn (I.prod I) I.tangent ∞ (minimizingDiagLog g hg) U := by
  obtain ⟨U, hU, hdiag, hs⟩ := exists_smooth_minimizingDiagLog_neighborhood g hg
  obtain ⟨ρ, hρ, hρU⟩ : ∃ ρ : ℝ≥0, 0 < ρ ∧
      ∀ x y, Manifold.riemannianEDist I x y ≤ (ρ : ℝ≥0∞) → (x, y) ∈ U := by
    let : PseudoEMetricSpace M := .ofRiemannianMetric I M
    exact DifferentialGeometry.Analysis.exists_uniform_diagonal_radius hU hdiag
  exact ⟨ρ, U, hρ, hU, hρU, hs⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_uniform_smooth_minimizingDiagLog then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_uniform_smooth_minimizingDiagLog"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_uniform_smooth_minimizingDiagLog ``Submission.DifferentialGeometry.Geometry.exists_uniform_smooth_minimizingDiagLog

end DifferentialGeometry.Geometry
