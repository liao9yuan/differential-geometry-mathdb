import Submission.DifferentialGeometry.Geometry.Metric.LocalCollapse
import Submission.DifferentialGeometry.Analysis.Calculus.Retraction.FiniteCover
import Mathlib.Geometry.Manifold.WhitneyEmbedding

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission










noncomputable section

open _root_.Set _root_.Filter _root_.Function _root_.Manifold
open scoped _root_.Topology _root_.ContDiff _root_.Manifold

namespace DifferentialGeometry.Geometry

section Boundaryless

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [Nonempty M]



theorem exists_smooth_neighborhood_retraction {e : M → F}
    (he : ContMDiff I 𝓘(ℝ, F) ∞ e) (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, _root_.Function.Injective (mfderiv I 𝓘(ℝ, F) e p)) :
    ∃ (r : F → M) (U : Set F), IsOpen U ∧ _root_.Set.range e ⊆ U ∧
      ContMDiffOn 𝓘(ℝ, F) I ∞ r U ∧ ∀ p, r (e p) = p := by
  classical
  choose Φ V hΦ hfix hV hpV hmap using
    (fun p => exists_smooth_local_collapse he hemb p (hi p))
  have hcover : _root_.Set.range e ⊆ ⋃ p, V p := by
    rintro _ ⟨p, rfl⟩
    exact mem_iUnion.mpr ⟨p, hpV p⟩
  have hS : IsCompact (_root_.Set.range e) := isCompact_range he.continuous
  obtain ⟨R, U, hR, hU, hSU, hRU, hRfix⟩ :=
    DifferentialGeometry.Analysis.exists_smooth_neighborhood_retraction_of_local hS Φ V hΦ
      (fun i q ⟨p, hp⟩ => hp ▸ hfix i p) hV hmap hcover
  let r : F → M := fun z => if h : R z ∈ _root_.Set.range e then Classical.choose h else Classical.arbitrary M
  have her (z : F) (hz : z ∈ U) : e (r z) = R z := by
    dsimp only [r]
    rw [dif_pos (hRU hz)]
    exact Classical.choose_spec (hRU hz)
  have hleft (p : M) : r (e p) = p := hemb.injective
    ((her (e p) (hSU (_root_.Set.mem_range_self p))).trans (hRfix (e p) (_root_.Set.mem_range_self p)))
  refine ⟨r, U, hU, hSU, ?_, hleft⟩
  intro z hz
  obtain ⟨r₀, W, hW, hpW, hr₀, hleft₀⟩ :=
    exists_local_retraction_of_embedding he hemb (r z) (hi (r z))
  have hRz : R z ∈ W := by rwa [her z hz] at hpW
  have hloc : r =ᶠ[𝓝 z] (r₀ ∘ R) := by
    filter_upwards [hU.mem_nhds hz, hR.continuous.continuousAt (hW.mem_nhds hRz)] with y hy hRy
    dsimp only [Function.comp_apply]
    rw [← her y hy]
    exact (hleft₀ (r y) (by rwa [her y hy])).symm
  have hsm : ContMDiffAt 𝓘(ℝ, F) I ∞ (r₀ ∘ R) z :=
    ((hr₀ (R z) hRz).contMDiffAt (hW.mem_nhds hRz)).comp z hR.contMDiff.contMDiffAt
  exact (hsm.congr_of_eventuallyEq hloc).contMDiffWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_smooth_neighborhood_retraction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_smooth_neighborhood_retraction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_smooth_neighborhood_retraction ``Submission.DifferentialGeometry.Geometry.exists_smooth_neighborhood_retraction

end Boundaryless

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [Nonempty M]

omit [Nonempty M] in
theorem exists_compact_smooth_embedding [T2Space M] :
    ∃ (n : ℕ) (e : M → EuclideanSpace ℝ (Fin n)),
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e ∧
      _root_.Topology.IsClosedEmbedding e ∧
      ∀ p, _root_.Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e p) :=
  exists_embedding_euclidean_of_compact (I := 𝓘(ℝ, E)) (M := M)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_compact_smooth_embedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_compact_smooth_embedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_compact_smooth_embedding ``Submission.DifferentialGeometry.Geometry.exists_compact_smooth_embedding



theorem exists_compact_embedding_and_retraction [T2Space M] :
    ∃ (n : ℕ) (e : M → EuclideanSpace ℝ (Fin n))
      (r : EuclideanSpace ℝ (Fin n) → M) (U : Set (EuclideanSpace ℝ (Fin n))),
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e ∧
      _root_.Topology.IsClosedEmbedding e ∧
      (∀ p, _root_.Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e p)) ∧
      IsOpen U ∧ _root_.Set.range e ⊆ U ∧
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) ∞ r U ∧
      ∀ p, r (e p) = p := by
  obtain ⟨n, e, he, hemb, hi⟩ := exists_compact_smooth_embedding (E := E) (M := M)
  obtain ⟨r, U, hU, heU, hr, hleft⟩ := exists_smooth_neighborhood_retraction he hemb.isEmbedding hi
  exact ⟨n, e, r, U, he, hemb, hi, hU, heU, hr, hleft⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_compact_embedding_and_retraction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_compact_embedding_and_retraction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_compact_embedding_and_retraction ``Submission.DifferentialGeometry.Geometry.exists_compact_embedding_and_retraction

end DifferentialGeometry.Geometry
