import Submission.DifferentialGeometry.Geometry.Metric.Construction.BumpExtension
import Submission.DifferentialGeometry.Geometry.Metric.Comparison.CompactLowerBound
import Submission.DifferentialGeometry.Geometry.Metric.Completeness
import Submission.DifferentialGeometry.Geometry.Metric.Euclidean

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

universe u uE uH

open scoped _root_.Manifold _root_.ContDiff _root_.Topology
open _root_.TopologicalSpace
open _root_.Bundle _root_.Submission.Bundle
open _root_.Manifold

namespace DifferentialGeometry

noncomputable def flatModelMetric
    (E : Type uE) [NormedAddCommGroup E] [InnerProductSpace Real E]
    :
    SmoothRiemannianMetric 𝓘(Real, E) E :=
  euclideanMetric

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.flatModelMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.flatModelMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.flatModelMetric ``Submission.DifferentialGeometry.flatModelMetric

namespace RiemannianMetricComplete

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

theorem of_eq_off_compact
    {g h : SmoothRiemannianMetric I M}
    (hg : RiemannianMetricComplete (I := I) g)
    {K : Set M} (hK : IsCompact K)
    (heq : ∀ x : M, x ∉ K → h.inner x = g.inner x) :
    RiemannianMetricComplete (I := I) h := by
  obtain ⟨c, hc, hlower⟩ := metric_lower_on (I := I) hK h g
  refine of_lower hg (lt_min hc one_pos) ?_
  intro x v
  have hgnonneg : 0 ≤ g.inner x v v := by
    by_cases hv : v = 0
    · subst hv
      simp
    · exact (g.pos x v hv).le
  by_cases hx : x ∈ K
  · exact (mul_le_mul_of_nonneg_right (min_le_left c 1) hgnonneg).trans
      (hlower x hx v)
  · rw [heq x hx]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (min_le_right c 1) hgnonneg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.RiemannianMetricComplete.of_eq_off_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.RiemannianMetricComplete.of_eq_off_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.RiemannianMetricComplete.of_eq_off_compact ``Submission.DifferentialGeometry.RiemannianMetricComplete.of_eq_off_compact

theorem bumpExtend_complete
    (R : SmoothRiemannianMetric I M)
    (hR : RiemannianMetricComplete (I := I) R)
    (U : _root_.TopologicalSpace.Opens M) [SigmaCompactSpace U] [T2Space U]
    (gU : SmoothRiemannianMetric I U) (χ : M → Real)
    (hχ : ContMDiff I 𝓘(Real, Real) ∞ χ)
    (hχ01 : ∀ x, χ x ∈ Set.Icc (0 : Real) 1)
    (hχsupport : tsupport χ ⊆ (U : Set M))
    (hχcomp : IsCompact (tsupport χ)) :
    RiemannianMetricComplete (I := I)
      (R.bumpExtendOpen (I := I) U gU χ hχ hχ01 hχsupport) := by
  apply of_eq_off_compact hR hχcomp
  intro x hx
  ext v w
  exact bumpExtendOpen_inner_of_notMem_tsupport
    (I := I) R U gU χ hχ hχ01 hχsupport x hx v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.RiemannianMetricComplete.bumpExtend_complete then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.RiemannianMetricComplete.bumpExtend_complete"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.RiemannianMetricComplete.bumpExtend_complete ``Submission.DifferentialGeometry.RiemannianMetricComplete.bumpExtend_complete

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem flatModel_complete
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
    [FiniteDimensional Real E] :
    RiemannianMetricComplete (I := 𝓘(Real, E)) (flatModelMetric E) := by
  simpa only [flatModelMetric] using euclideanMetric_complete (E := E)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.RiemannianMetricComplete.flatModel_complete then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.RiemannianMetricComplete.flatModel_complete"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.RiemannianMetricComplete.flatModel_complete ``Submission.DifferentialGeometry.RiemannianMetricComplete.flatModel_complete

end RiemannianMetricComplete
end DifferentialGeometry

end
