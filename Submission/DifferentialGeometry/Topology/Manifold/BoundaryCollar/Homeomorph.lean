import Submission.DifferentialGeometry.Topology.Manifold.BoundaryCollar.CollarStrip

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Function _root_.Filter _root_.Manifold _root_.Topology
open scoped _root_.ContDiff
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.Manifold.BoundaryCollar


def halfOpenStrip {B M : Type*} {ε δ : ℝ} (c : B × _root_.Set.Icc (0 : ℝ) ε → M)
    (hδε : δ ≤ ε) : B × _root_.Set.Ico (0 : ℝ) δ → M :=
  fun q => c (q.1, ⟨q.2, q.2.2.1, q.2.2.2.le.trans hδε⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.BoundaryCollar.halfOpenStrip then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.BoundaryCollar.halfOpenStrip"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.BoundaryCollar.halfOpenStrip ``Submission.DifferentialGeometry.Manifold.BoundaryCollar.halfOpenStrip


theorem range_halfOpenStrip {B M : Type*} {ε δ : ℝ}
    (c : B × _root_.Set.Icc (0 : ℝ) ε → M) (hδε : δ ≤ ε) :
    range (halfOpenStrip c hδε) = c '' {q | (q.2 : ℝ) < δ} := by
  ext y
  constructor
  · rintro ⟨⟨b, t⟩, rfl⟩
    exact ⟨(b, ⟨t, t.2.1, t.2.2.le.trans hδε⟩), t.2.2, rfl⟩
  · rintro ⟨⟨b, t⟩, ht, rfl⟩
    exact ⟨(b, ⟨t, t.2.1, ht⟩), rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.BoundaryCollar.range_halfOpenStrip then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.BoundaryCollar.range_halfOpenStrip"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.BoundaryCollar.range_halfOpenStrip ``Submission.DifferentialGeometry.Manifold.BoundaryCollar.range_halfOpenStrip


theorem isEmbedding_halfOpenStrip {B M : Type*} [TopologicalSpace B] [TopologicalSpace M]
    {ε δ : ℝ} {c : B × _root_.Set.Icc (0 : ℝ) ε → M} (hc : _root_.Topology.IsEmbedding c) (hδε : δ ≤ ε) :
    IsEmbedding (halfOpenStrip c hδε) := by
  have hsub : _root_.Set.Ico (0 : ℝ) δ ⊆ _root_.Set.Icc (0 : ℝ) ε := fun _ ht => ⟨ht.1, ht.2.le.trans hδε⟩
  exact hc.comp (IsEmbedding.id.prodMap (IsEmbedding.inclusion hsub))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.BoundaryCollar.isEmbedding_halfOpenStrip then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.BoundaryCollar.isEmbedding_halfOpenStrip"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.BoundaryCollar.isEmbedding_halfOpenStrip ``Submission.DifferentialGeometry.Manifold.BoundaryCollar.isEmbedding_halfOpenStrip

theorem exists_boundary_collar_homeomorph
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    (hK : IsCompact ((𝓡∂ (n + 1)).boundary M)) :
    ∃ (δ : ℝ) (hδ : 0 < δ) (U : TopologicalSpace.Opens M),
      (𝓡∂ (n + 1)).boundary M ⊆ U ∧
      ∃ e : (BoundaryManifold (𝓡∂ (n + 1)) M × _root_.Set.Ico (0 : ℝ) δ) ≃ₜ U,
        (∀ p, (e (p, ⟨0, ⟨le_rfl, hδ⟩⟩) : M) = boundaryInclusion (𝓡∂ (n + 1)) M p) ∧
        ∀ p (t : _root_.Set.Ico (0 : ℝ) δ), 0 < (t : ℝ) →
          (𝓡∂ (n + 1)).IsInteriorPoint (e (p, t) : M) := by
  obtain ⟨ε, hε, hc⟩ := exists_smooth_boundary_collar_strip hK
  let : Fact ((0 : ℝ) < ε) := ⟨hε⟩
  obtain ⟨c, hclosed, _, hzero, hi, δ, hδ, hδε, hopen, hboundary⟩ := hc
  let f := halfOpenStrip c hδε.le
  have hf : _root_.Topology.IsEmbedding f := isEmbedding_halfOpenStrip hclosed.isEmbedding hδε.le
  let U : TopologicalSpace.Opens M := ⟨range f, by rw [range_halfOpenStrip]; exact hopen⟩
  refine ⟨δ, hδ, U, ?_, hf.toHomeomorph, ?_, ?_⟩
  · intro p hp
    change p ∈ _root_.Set.range f
    rw [range_halfOpenStrip]
    exact hboundary hp
  · intro p
    change c (p, ⟨0, ⟨le_rfl, hε.le⟩⟩) = boundaryInclusion (𝓡∂ (n + 1)) M p
    exact hzero p
  · intro p t ht
    exact hi p ⟨t, t.2.1, t.2.2.le.trans hδε.le⟩ ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.BoundaryCollar.exists_boundary_collar_homeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.BoundaryCollar.exists_boundary_collar_homeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.BoundaryCollar.exists_boundary_collar_homeomorph ``Submission.DifferentialGeometry.Manifold.BoundaryCollar.exists_boundary_collar_homeomorph

end DifferentialGeometry.Manifold.BoundaryCollar
