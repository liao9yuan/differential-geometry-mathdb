import Submission.DifferentialGeometry.Topology.SphereSeparation.Innermost
import Submission.DifferentialGeometry.Topology.Manifold.PuncturedSphereChart
import Submission.DifferentialGeometry.Topology.Manifold.PartialChartEmbedding
import Submission.DifferentialGeometry.Topology.ThreeManifold.SmoothSchoenflies
import Submission.DifferentialGeometry.Topology.SphereSeparation.SmoothSchoenfliesBallFilling

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.Topology.SphereSeparation

variable {ι : Type*} [Finite ι] [Nonempty ι]

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S3" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

theorem exists_innermost_ball_of_sphere_family
    (e : ι → SphereTwo → S3)
    (he : ∀ i, Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (e i))
    (hdis : Pairwise fun i j => Disjoint (_root_.Set.range (e i)) (_root_.Set.range (e j)))
    (north : S3) (hnorth : ∀ i, north ∉ _root_.Set.range (e i)) :
    ∃ i : ι, ∃ F : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 S3 ∞,
      F.source = _root_.Set.univ ∧ F '' Metric.sphere (0 : E3) 1 = _root_.Set.range (e i) ∧
      Disjoint (F '' Metric.ball (0 : E3) 1) (⋃ j, _root_.Set.range (e j)) := by
  let _ : ConnectedSpace SphereTwo := Subtype.connectedSpace
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp)) (0 : E3) zero_le_one)
  obtain ⟨c, hcsource, hctarget⟩ := Manifold.exists_smooth_punctured_sphere_chart 3 north
  have hsource (i : ι) : _root_.Set.range (e i) ⊆ c.source := by
    rw [hcsource]
    intro y hy hyN
    exact hnorth i (hyN ▸ hy)
  let f (i : ι) := c ∘ e i
  have hf (i : ι) : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (f i) :=
    isSmoothEmbedding_comp_partialDiffeomorph c (he i) (hsource i)
  have hfdis : Pairwise fun i j => Disjoint (_root_.Set.range (f i)) (_root_.Set.range (f j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    rintro y ⟨z, hz⟩ ⟨w, hw⟩
    have heq : e i z = e j w := c.toPartialEquiv.injOn
      (hsource i (_root_.Set.mem_range_self z)) (hsource j (_root_.Set.mem_range_self w)) (hz.trans hw.symm)
    exact (hdis hij).le_bot ⟨mem_range_self z, w, heq.symm⟩
  let d (i : ι) := (jordanBrouwer_openThreeSpace (f i) (hf i)
    (Diffeomorph.refl (𝓡 3) E3 ∞)).toSphereSides
  obtain ⟨i, havoid, _hclosed⟩ := exists_sphereSides_compactSide_disjoint_iUnion d
    (fun j => isConnected_range (hf j).contMDiff.continuous) hfdis
  have hSch : smoothSchoenfliesThree := by
    intro e he
    obtain ⟨D, hD⟩ := ThreeManifold.smooth_schoenflies_three e he
    exact ⟨D.toPartialDiffeomorph, _root_.Set.subset_univ _, hD⟩
  obtain ⟨D, hD⟩ := (smoothSchoenfliesThree_iff_smoothSchoenfliesBallFilling.mp hSch) (f i) (hf i)
  have hsphere : D '' Metric.sphere (0 : E3) 1 = _root_.Set.range (f i) := by
    rw [← frontier_ball (0 : E3) one_ne_zero]
    change D.toHomeomorph '' frontier (Metric.ball (0 : E3) 1) = _
    rw [D.toHomeomorph.image_frontier]
    change frontier (D '' Metric.ball (0 : E3) 1) = _
    rw [hD]
    exact (d i).frontier_compactSide
  let F := D.toPartialDiffeomorph.trans c.symm
  have hFsource : F.source = univ := by
    ext y
    change (y ∈ (_root_.Set.univ : Set E3) ∧ D y ∈ c.target) ↔ y ∈ (_root_.Set.univ : Set E3)
    rw [hctarget]
    simp
  have hFimage (A : Set E3) : F '' A = c.symm '' (D '' A) := by
    change (c.symm ∘ D) '' A = _
    exact _root_.Set.image_comp _ _ _
  refine ⟨i, F, hFsource, ?_, ?_⟩
  · rw [hFimage, hsphere, _root_.Set.range_comp]
    ext y
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      change c.invFun (c z) ∈ _root_.Set.range (e i)
      rw [c.left_inv' (hsource i hz)]
      exact hz
    · rintro ⟨z, rfl⟩
      exact ⟨c (e i z), ⟨e i z, _root_.Set.mem_range_self z, rfl⟩,
        c.left_inv' (hsource i (_root_.Set.mem_range_self z))⟩
  · rw [hFimage, hD, Set.disjoint_left]
    rintro y ⟨z, hz, rfl⟩ hy
    obtain ⟨j, w, hw⟩ := mem_iUnion.mp hy
    have hztarget : z ∈ c.target := by rw [hctarget]; trivial
    have hfz : f j w = z := by
      change c (e j w) = z
      rw [hw]
      exact c.right_inv' hztarget
    exact havoid.le_bot ⟨hz, mem_iUnion.mpr ⟨j, w, hfz⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exists_innermost_ball_of_sphere_family then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exists_innermost_ball_of_sphere_family"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exists_innermost_ball_of_sphere_family ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_innermost_ball_of_sphere_family

end DifferentialGeometry.Topology.SphereSeparation

end

end
