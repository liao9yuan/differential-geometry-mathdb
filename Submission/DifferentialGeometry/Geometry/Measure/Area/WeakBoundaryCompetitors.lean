import Submission.DifferentialGeometry.Geometry.Measure.Area.LeastAreaWeakBoundary

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.DifferentialGeometry _root_.Function _root_.Submission.Function
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [FiniteDimensional ℝ E] [CompactSpace M] in
theorem diskTrace_riemannian_lipschitz (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {u : C(closedDisk, M)} {K : ℝ≥0}
    (hu : ∀ z w, riemannianEDistOf g (u z) (u w) ≤ (K : ℝ≥0∞) * _root_.EDist.edist z w) :
    ∃ L : ℝ≥0, ∀ s t, riemannianEDistOf g (diskTrace u s) (diskTrace u t) ≤
      (L : ℝ≥0∞) * _root_.EDist.edist s t := by
  let cg := g.toContinuousRiemannianMetric
  let : _root_.Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨cg.toRiemannianMetric⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  have hu' : LipschitzWith K u := hu
  have hb : LipschitzWith ⟨2 * Real.pi, by positivity⟩ diskBoundary := by
    intro s t
    exact circle_boundary_lipschitz s t
  exact ⟨_, hu'.comp hb⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.diskTrace_riemannian_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.diskTrace_riemannian_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.diskTrace_riemannian_lipschitz ``Submission.DifferentialGeometry.Geometry.diskTrace_riemannian_lipschitz



def weakSpanningDiskCompetitors (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : freeLoop M) :
    Set C(closedDisk, M) :=
  {u | ∃ (ψ : ℝ → ℝ) (hc : Continuous ψ) (hp : ∀ t, ψ (t + 1) = ψ t + 1),
    Monotone ψ ∧ u ∈ spanningDiskCompetitors g (γ.comp (affineCircleMap ψ hc hp))}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.weakSpanningDiskCompetitors then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.weakSpanningDiskCompetitors"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.weakSpanningDiskCompetitors ``Submission.DifferentialGeometry.Geometry.weakSpanningDiskCompetitors

omit [FiniteDimensional ℝ E] [CompactSpace M] [T3Space M] in
theorem spanningDiskCompetitors_subset_weak (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : freeLoop M) : spanningDiskCompetitors g γ ⊆ weakSpanningDiskCompetitors g γ := by
  intro u hu
  have hp : ∀ t : ℝ, id (t + 1) = id t + 1 := fun _ => rfl
  refine ⟨id, continuous_id, hp, monotone_id, ?_⟩
  have heq : γ.comp (affineCircleMap id continuous_id hp) = γ := by
    ext θ
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
    rfl
  rw [heq]
  exact hu

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.spanningDiskCompetitors_subset_weak then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.spanningDiskCompetitors_subset_weak"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.spanningDiskCompetitors_subset_weak ``Submission.DifferentialGeometry.Geometry.spanningDiskCompetitors_subset_weak

variable [Nonempty M] [PreconnectedSpace M]



theorem leastSpanningArea_le_weak_competitor (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : lipschitzContractibleLoop g) {u : C(closedDisk, M)}
    (hu : u ∈ weakSpanningDiskCompetitors g γ.val.val) :
    leastSpanningArea g γ ≤ riemannianDiskArea g u := by
  obtain ⟨ψ, hc, hp, hm, ht, K, hK⟩ := hu
  let δ : lipschitzContractibleLoop g :=
    ⟨⟨diskTrace u, diskTrace_nullhomotopic u⟩, diskTrace_riemannian_lipschitz g hK⟩
  have harea := leastSpanningArea_comp_monotone_lift g γ δ hc hm hp ht
  rw [← harea]
  exact leastSpanningArea_le_competitor g δ ⟨rfl, K, hK⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.leastSpanningArea_le_weak_competitor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.leastSpanningArea_le_weak_competitor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.leastSpanningArea_le_weak_competitor ``Submission.DifferentialGeometry.Geometry.leastSpanningArea_le_weak_competitor


def weakSpanningDiskAreas (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : lipschitzContractibleLoop g) : Set ℝ :=
  (fun u : C(closedDisk, M) => riemannianDiskArea g u) '' weakSpanningDiskCompetitors g γ.val.val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.weakSpanningDiskAreas then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.weakSpanningDiskAreas"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.weakSpanningDiskAreas ``Submission.DifferentialGeometry.Geometry.weakSpanningDiskAreas


theorem weakSpanningDiskAreas_nonempty (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : lipschitzContractibleLoop g) : (weakSpanningDiskAreas g γ).Nonempty := by
  obtain ⟨a, u, hu, rfl⟩ := spanningDiskAreas_nonempty g γ
  exact ⟨_, u, spanningDiskCompetitors_subset_weak g γ.val.val hu, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.weakSpanningDiskAreas_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.weakSpanningDiskAreas_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.weakSpanningDiskAreas_nonempty ``Submission.DifferentialGeometry.Geometry.weakSpanningDiskAreas_nonempty


theorem weakSpanningDiskAreas_isGLB (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : lipschitzContractibleLoop g) : IsGLB (weakSpanningDiskAreas g γ) (leastSpanningArea g γ) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact leastSpanningArea_le_weak_competitor g γ hu
  · intro b hb
    apply (leastSpanningArea_isGLB g γ).2
    rintro a ⟨u, hu, rfl⟩
    exact hb ⟨u, spanningDiskCompetitors_subset_weak g γ.val.val hu, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.weakSpanningDiskAreas_isGLB then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.weakSpanningDiskAreas_isGLB"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.weakSpanningDiskAreas_isGLB ``Submission.DifferentialGeometry.Geometry.weakSpanningDiskAreas_isGLB



theorem sInf_weakSpanningDiskAreas (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : lipschitzContractibleLoop g) : _root_.InfSet.sInf (weakSpanningDiskAreas g γ) = leastSpanningArea g γ :=
  (weakSpanningDiskAreas_isGLB g γ).csInf_eq (weakSpanningDiskAreas_nonempty g γ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.sInf_weakSpanningDiskAreas then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.sInf_weakSpanningDiskAreas"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.sInf_weakSpanningDiskAreas ``Submission.DifferentialGeometry.Geometry.sInf_weakSpanningDiskAreas

end DifferentialGeometry.Geometry
