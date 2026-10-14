import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Geometry.Manifold.Instances.Sphere
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false

open _root_.Set
open scoped _root_.Manifold _root_.ContDiff

namespace PartialDiffeomorph
open _root_.PartialDiffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F H'}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H' N] [T2Space N] {n : ℕ∞ω}

open _root_.PartialDiffeomorph in
theorem image_frontier_of_isCompact (P : PartialDiffeomorph I J M N n)
    {K : Set M} (hK : IsCompact K) (hsrc : K ⊆ P.source) :
    P '' frontier K = frontier (P '' K) := by
  have himg : P.toOpenPartialHomeomorph.IsImage K (P '' K) := by
    apply OpenPartialHomeomorph.IsImage.of_image_eq
    change P '' (P.source ∩ K) = P.target ∩ (P '' K)
    have ht : P '' K ⊆ P.target := by
      rintro y ⟨x, hx, rfl⟩
      exact P.map_source' (hsrc hx)
    rw [inter_eq_right.mpr hsrc, inter_eq_right.mpr ht]
  have hcompact : IsCompact (P '' K) :=
    hK.image_of_continuousOn (P.contMDiffOn_toFun.continuousOn.mono hsrc)
  have hfs : frontier K ⊆ P.source := hK.isClosed.frontier_subset.trans hsrc
  have hft : frontier (P '' K) ⊆ P.target := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hcompact.isClosed.frontier_subset hy
    exact P.map_source' (hsrc hx)
  have h := himg.frontier.image_eq
  change P '' (P.source ∩ frontier K) = P.target ∩ frontier (P '' K) at h
  simpa only [inter_eq_right.mpr hfs, inter_eq_right.mpr hft] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.image_frontier_of_isCompact then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.image_frontier_of_isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.image_frontier_of_isCompact ``Submission.PartialDiffeomorph.image_frontier_of_isCompact

end PartialDiffeomorph

end

section

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Metric
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.Manifold

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {Z : Type*} [TopologicalSpace Z] [ChartedSpace E3 Z] [T2Space Z]

theorem closure_image_ball_of_partialDiffeomorph
    (b : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Z ∞)
    (hb : _root_.Metric.closedBall (0 : E3) 1 ⊆ b.source) :
    closure (b '' _root_.Metric.ball (0 : E3) 1) = b '' _root_.Metric.closedBall (0 : E3) 1 := by
  have hcont := b.contMDiffOn_toFun.continuousOn.mono hb
  apply subset_antisymm
  · exact closure_minimal (_root_.Set.image_mono _root_.Metric.ball_subset_closedBall)
      ((_root_.ProperSpace.isCompact_closedBall (0 : E3) 1).image_of_continuousOn hcont).isClosed
  · have hcont' : ContinuousOn b (closure (_root_.Metric.ball (0 : E3) 1)) := by
      simpa only [closure_ball _ one_ne_zero] using hcont
    simpa only [closure_ball _ one_ne_zero] using hcont'.image_closure

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.closure_image_ball_of_partialDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.closure_image_ball_of_partialDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.closure_image_ball_of_partialDiffeomorph ``Submission.DifferentialGeometry.Topology.Manifold.closure_image_ball_of_partialDiffeomorph

theorem frontier_image_ball_of_partialDiffeomorph
    (b : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Z ∞)
    (hb : _root_.Metric.closedBall (0 : E3) 1 ⊆ b.source) :
    frontier (b '' _root_.Metric.ball (0 : E3) 1) = b '' _root_.Metric.sphere (0 : E3) 1 := by
  have hbc := ball_subset_closedBall.trans hb
  have hcl := closure_image_ball_of_partialDiffeomorph b hb
  have ho : IsOpen (b '' _root_.Metric.ball (0 : E3) 1) := b.toOpenPartialHomeomorph.isOpen_image_of_subset_source _root_.Metric.isOpen_ball hbc
  rw [frontier, hcl, ho.interior_eq]
  apply subset_antisymm
  · rintro y ⟨⟨z, hz, rfl⟩, hnot⟩
    refine ⟨z, ?_, rfl⟩
    exact le_antisymm hz (not_lt.mp fun h => hnot (_root_.Set.mem_image_of_mem b h))
  · rintro y ⟨z, hz, rfl⟩
    have hzc := _root_.Metric.sphere_subset_closedBall hz
    refine ⟨mem_image_of_mem b hzc, ?_⟩
    rintro ⟨w, hw, heq⟩
    have hwz : w = z := b.toPartialEquiv.injOn (hbc hw) (hb hzc) heq
    subst w
    exact (ne_of_lt hw) hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.frontier_image_ball_of_partialDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.frontier_image_ball_of_partialDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.frontier_image_ball_of_partialDiffeomorph ``Submission.DifferentialGeometry.Topology.Manifold.frontier_image_ball_of_partialDiffeomorph

theorem image_sphere_eq_frontier_of_ball_complement
    {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [T2Space M]
    (b : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Z ∞)
    (P : PartialDiffeomorph (𝓡 3) (𝓡 3) Z M ∞)
    (hb : _root_.Metric.closedBall (0 : E3) 1 ⊆ b.source)
    (hK : IsCompact (b '' _root_.Metric.ball (0 : E3) 1)ᶜ)
    (hP : (b '' _root_.Metric.ball (0 : E3) 1)ᶜ ⊆ P.source) :
    P '' (b '' _root_.Metric.sphere (0 : E3) 1) = frontier (P '' (b '' _root_.Metric.ball (0 : E3) 1)ᶜ) := by
  rw [← P.image_frontier_of_isCompact hK hP, frontier_compl,
    frontier_image_ball_of_partialDiffeomorph b hb]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.image_sphere_eq_frontier_of_ball_complement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.image_sphere_eq_frontier_of_ball_complement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.image_sphere_eq_frontier_of_ball_complement ``Submission.DifferentialGeometry.Topology.Manifold.image_sphere_eq_frontier_of_ball_complement

end DifferentialGeometry.Topology.Manifold

end

end
