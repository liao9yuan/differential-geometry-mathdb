import Submission.DifferentialGeometry.Geometry.Metric.Family.DistanceContinuity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_compact_convex_source_riemannian_lipschitz
    (g : SmoothRiemannianMetric I M) {f : V → M} {s S : Set V}
    (hf : ContMDiffOn 𝓘(ℝ, V) I 1 f s) (hs : UniqueMDiffOn 𝓘(ℝ, V) s)
    (hS : IsCompact S) (hconv : Convex ℝ S) (hSs : S ⊆ s) :
    ∃ C : ℝ≥0, ∀ x ∈ S, ∀ y ∈ S,
      riemannianEDistOf g (f x) (f y) ≤ (C : ℝ≥0∞) * _root_.EDist.edist x y := by
  have hquad : Continuous (metricTimeBundleQuad (fun _ : ℝ => g) ({0} : Set ℝ)) :=
    (metricQuad_cont g).comp continuous_snd
  obtain ⟨L, hL, hbound⟩ := exists_sqrt_inner_mfderivWithin_le_of_isCompact
    (fun _ : ℝ => g) (isCompact_singleton (x := (0 : ℝ))) hquad
    hf hs.uniqueDiffOn hSs hS
  have hLnonneg : 0 ≤ L := zero_le_one.trans hL
  refine ⟨⟨L, hLnonneg⟩, fun x hx y hy => ?_⟩
  let : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hspeed : ∀ w ∈ S, ∀ v : V,
      ‖mfderivWithin 𝓘(ℝ, V) I f s w v‖ₑ ≤ ENNReal.ofReal (L * ‖v‖) := by
    intro w hw v
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    exact ENNReal.ofReal_le_ofReal (hbound 0 (_root_.Set.mem_singleton 0) w hw v)
  have hdist := DifferentialGeometry.riemannianEDist_le_of_mfderivWithin_le
    hf hSs hspeed (hconv.segment_subset hx hy)
  change Manifold.riemannianEDist I (f x) (f y) ≤ _
  convert hdist using 1
  rw [ENNReal.ofReal_mul hLnonneg, ENNReal.ofReal_eq_coe_nnreal hLnonneg, edist_dist]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_compact_convex_source_riemannian_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_compact_convex_source_riemannian_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_compact_convex_source_riemannian_lipschitz ``Submission.DifferentialGeometry.Geometry.exists_compact_convex_source_riemannian_lipschitz

end DifferentialGeometry.Geometry
