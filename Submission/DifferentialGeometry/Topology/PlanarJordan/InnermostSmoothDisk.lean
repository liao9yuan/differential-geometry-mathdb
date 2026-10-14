import Submission.DifferentialGeometry.Topology.PlanarJordan.SmoothSchoenflies

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set _root_.Metric
open scoped _root_.ContDiff _root_.Submission.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Topology.PlanarJordan

theorem exists_innermost_smooth_disk
    {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (e : ι → AddCircle (1 : ℝ) → Schoenflies.Plane)
    (he : ∀ i ∈ s, Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ (e i))
    (hdisjoint : (s : Set ι).Pairwise fun i j => Disjoint (_root_.Set.range (e i)) (_root_.Set.range (e j))) :
    ∃ i ∈ s, ∃ Φ : Schoenflies.Plane ≃ₘ[ℝ] Schoenflies.Plane,
      Φ '' _root_.Metric.sphere (0 : Schoenflies.Plane) 1 = _root_.Set.range (e i) ∧
      Φ '' _root_.Metric.ball (0 : Schoenflies.Plane) 1 = Schoenflies.inside (_root_.Set.range (e i)) ∧
      Φ '' _root_.Metric.closedBall (0 : Schoenflies.Plane) 1 =
        closure (Schoenflies.inside (_root_.Set.range (e i))) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ j ∈ s, j ≠ i →
        Disjoint (_root_.Metric.cthickening δ (Φ '' _root_.Metric.closedBall (0 : Schoenflies.Plane) 1))
          (_root_.Set.range (e j)) := by
  let r := Complex.orthonormalBasisOneI.repr
  let a : Circle ≃ₜ _root_.Metric.sphere (0 : Schoenflies.Plane) 1 :=
    r.toHomeomorph.subtype (fun z => by
      change z ∈ _root_.Metric.sphere (0 : ℂ) 1 ↔ r z ∈ _root_.Metric.sphere 0 1
      rw [mem_sphere_zero_iff_norm, mem_sphere_zero_iff_norm, r.norm_map])
  let q : _root_.Metric.sphere (0 : Schoenflies.Plane) 1 ≃ₜ AddCircle (1 : ℝ) :=
    a.symm.trans (AddCircle.homeomorphCircle one_ne_zero).symm
  let f := fun i => e i ∘ q
  have hfe (i : ι) (hi : i ∈ s) : Topology.IsEmbedding (f i) :=
    (he i hi).isEmbedding.comp q.isEmbedding
  have hrange (i : ι) : _root_.Set.range (f i) = _root_.Set.range (e i) := by
    dsimp only [f]
    rw [_root_.Set.range_comp, q.surjective.range_eq, _root_.Set.image_univ]
  have hfd : (s : Set ι).Pairwise fun i j => Disjoint (_root_.Set.range (f i)) (_root_.Set.range (f j)) := by
    intro i hi j hj hij
    rw [hrange, hrange]
    exact hdisjoint hi hj hij
  obtain ⟨i, hi, F, _, _, hclosed, δ, hδ, hclear⟩ :=
    exists_innermost_circle_disk s hs f hfe hfd
  obtain ⟨Φ, hΦ, hball, hΦclosed⟩ := smooth_schoenflies (he i hi)
  have hdisk : Φ '' _root_.Metric.closedBall (0 : Schoenflies.Plane) 1 =
      F '' _root_.Metric.closedBall (0 : Schoenflies.Plane) 1 := by
    rw [hΦclosed, hclosed, hrange]
  refine ⟨i, hi, Φ, hΦ, hball, hΦclosed, δ, hδ, ?_⟩
  intro j hj hji
  rw [hdisk, ← hrange j]
  exact hclear j hj hji

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PlanarJordan.exists_innermost_smooth_disk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PlanarJordan.exists_innermost_smooth_disk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PlanarJordan.exists_innermost_smooth_disk ``Submission.DifferentialGeometry.Topology.PlanarJordan.exists_innermost_smooth_disk

end DifferentialGeometry.Topology.PlanarJordan
