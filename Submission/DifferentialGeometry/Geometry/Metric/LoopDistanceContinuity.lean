import Submission.DifferentialGeometry.Geometry.Metric.LoopDistance

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.Uniformity

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M] [PreconnectedSpace M]

omit [T3Space M] [PreconnectedSpace M] in
theorem riemannianLoopDistance_self (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : freeLoop M) :
    riemannianLoopDistance g γ γ = 0 := by
  simp [riemannianLoopDistance, riemannianEDistOf_self]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianLoopDistance_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianLoopDistance_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianLoopDistance_self ``Submission.DifferentialGeometry.Geometry.riemannianLoopDistance_self

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem continuous_riemannianLoopDistance {X : Type*} [TopologicalSpace X]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Γ Δ : X → freeLoop M}
    (hΓ : Continuous Γ) (hΔ : Continuous Δ) :
    Continuous (fun x => (riemannianLoopDistance g (Γ x) (Δ x) : ℝ)) := by
  let : _root_.Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  let : MetricSpace M := EMetricSpace.toMetricSpace DifferentialGeometry.Analysis.edist_ne_top_of_preconnected
  have hd (γ₀ γ₁ : freeLoop M) : (riemannianLoopDistance g γ₀ γ₁ : ℝ) = _root_.Dist.dist γ₀ γ₁ := by
    rw [riemannianLoopDistance_eq_iSup]
    change (⨆ θ, (_root_.EDist.edist (γ₀ θ) (γ₁ θ)).toReal) = _root_.Dist.dist γ₀ γ₁
    simpa only [edist_dist, ENNReal.toReal_ofReal dist_nonneg] using!
      (ContinuousMap.dist_eq_iSup (f := γ₀) (g := γ₁)).symm
  exact (hΓ.dist hΔ).congr (fun x => (hd (Γ x) (Δ x)).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.continuous_riemannianLoopDistance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.continuous_riemannianLoopDistance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.continuous_riemannianLoopDistance ``Submission.DifferentialGeometry.Geometry.continuous_riemannianLoopDistance

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [PreconnectedSpace M] in
theorem eventually_forall_riemannianEDist_lt (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ₀ : freeLoop M) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∀ᶠ γ : freeLoop M in 𝓝 γ₀, ∀ θ : loopCircle, riemannianEDistOf g (γ θ) (γ₀ θ) < ε := by
  let : _root_.Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let metricM : EMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  have hed : ∀ x y : M, _root_.EDist.edist x y = riemannianEDistOf g x y := fun _ _ => rfl
  have hV : {p : M × M | _root_.EDist.edist p.1 p.2 < ε} ∈ uniformity M :=
    (mem_uniformity_edist).mpr ⟨ε, hε, fun {_ _} h => h⟩
  have hE : {fg : freeLoop M × freeLoop M |
      ∀ x ∈ (_root_.Set.univ : Set loopCircle),
        (fg.1 x, fg.2 x) ∈ {p : M × M | _root_.EDist.edist p.1 p.2 < ε}} ∈
      uniformity (freeLoop M) := by
    rw [ContinuousMap.mem_compactConvergence_entourage_iff]
    exact ⟨univ, {p : M × M | _root_.EDist.edist p.1 p.2 < ε}, isCompact_univ, hV, subset_rfl⟩
  filter_upwards [UniformSpace.ball_mem_nhds γ₀ hE] with γ hγ θ
  have h : riemannianEDistOf g (γ₀ θ) (γ θ) < ε := by
    simpa only [hed] using hγ θ (_root_.Set.mem_univ θ)
  rwa [riemannianEDistOf_comm] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.eventually_forall_riemannianEDist_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.eventually_forall_riemannianEDist_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.eventually_forall_riemannianEDist_lt ``Submission.DifferentialGeometry.Geometry.eventually_forall_riemannianEDist_lt

end DifferentialGeometry.Geometry
