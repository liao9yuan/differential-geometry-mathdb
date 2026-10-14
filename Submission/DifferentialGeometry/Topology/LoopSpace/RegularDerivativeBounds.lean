import Submission.DifferentialGeometry.Topology.LoopSpace.RegularBounds
import Submission.DifferentialGeometry.Geometry.Metric.CurveLength

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.ContinuousMap _root_.Manifold _root_.Submission.Manifold _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry
open scoped _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Bundle _root_.Submission.Bundle _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M] [Nonempty M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_regular_loop_lipschitz_factor (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (e : M → F) (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, _root_.Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e p)) :
    ∃ C : ℝ≥0, ∀ (γ : regularLoop E M) (θ η : loopCircle),
      riemannianEDistOf g (γ.val θ) (γ.val η) ≤
        ((C * ‖regularLoopDerivative e (he.of_le (by exact_mod_cast le_top)) γ‖₊ : ℝ≥0) : ℝ≥0∞) *
          edist θ η := by
  let he₁ := he.of_le (show (1 : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) by exact_mod_cast le_top)
  obtain ⟨r, U, hU, heU, hr, hleft⟩ := exists_smooth_neighborhood_retraction he hemb hi
  obtain ⟨C, hC⟩ := exists_compact_source_curve_lipschitz g hU
    (hr.of_le (by exact_mod_cast le_top)) (isCompact_range he.continuous) heU
  let cg := g.toContinuousRiemannianMetric
  let : _root_.Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨cg.toRiemannianMetric⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  refine ⟨C, fun γ θ η => ?_⟩
  let D := ‖regularLoopDerivative e he₁ γ‖₊
  have hLip : LipschitzWith D (fun t : ℝ => e (γ.val (t : loopCircle))) := by
    apply lipschitzWith_of_nnnorm_deriv_le ((regularLoop_embedded_contDiff e he₁ γ).differentiable one_ne_zero)
    intro t
    exact_mod_cast (regularLoopDerivative e he₁ γ).norm_coe_le_norm (t : loopCircle)
  have hlift : LipschitzWith (C * D) (fun t : ℝ => γ.val (t : loopCircle)) := by
    intro x y
    have h := hC D (fun t : ℝ => e (γ.val (t : loopCircle)))
      (regularLoop_embedded_contDiff e he₁ γ) hLip (fun _ => _root_.Set.mem_range_self _) x y
    simpa only [hleft] using! h
  exact loop_lipschitz_of_lift hlift θ η

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_regular_loop_lipschitz_factor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_regular_loop_lipschitz_factor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_regular_loop_lipschitz_factor ``Submission.DifferentialGeometry.Topology.exists_regular_loop_lipschitz_factor



theorem regularLoop_riemannian_lipschitz (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : regularLoop E M) :
    ∃ L : ℝ≥0, ∀ θ η, riemannianEDistOf g (γ.val θ) (γ.val η) ≤ (L : ℝ≥0∞) * _root_.EDist.edist θ η := by
  obtain ⟨n, e, _, _, he, hemb, hi, _⟩ := exists_compact_embedding_and_retraction (E := E) (M := M)
  obtain ⟨C, hC⟩ := exists_regular_loop_lipschitz_factor g e he hemb.isEmbedding hi
  exact ⟨_, hC γ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.regularLoop_riemannian_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.regularLoop_riemannian_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.regularLoop_riemannian_lipschitz ``Submission.DifferentialGeometry.Topology.regularLoop_riemannian_lipschitz

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompactSpace M] [Nonempty M] in
theorem loop_arclength_le_of_riemannian_lipschitz
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : loopCircle → M} {L : ℝ≥0}
    (hγ : ∀ θ η, riemannianEDistOf g (γ θ) (γ η) ≤ (L : ℝ≥0∞) * _root_.EDist.edist θ η) :
    riemannianCurveLength g (fun t : ℝ => γ (t : loopCircle)) 0 1 ≤ L := by
  let cg := g.toContinuousRiemannianMetric
  let : _root_.Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨cg.toRiemannianMetric⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  have hγ' : LipschitzWith L γ := hγ
  have hlift : LipschitzWith L (fun t : ℝ => γ (t : loopCircle)) := by
    simpa only [mul_one, Function.comp_def] using! hγ'.comp loopCircle_projection_lipschitz
  have h := riemannianCurveELength_le_of_lipschitz g hlift 0 1
  simp only [sub_zero, ENNReal.ofReal_one, mul_one] at h
  exact (ENNReal.toReal_mono ENNReal.coe_ne_top h).trans_eq (ENNReal.coe_toReal L)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.loop_arclength_le_of_riemannian_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.loop_arclength_le_of_riemannian_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.loop_arclength_le_of_riemannian_lipschitz ``Submission.DifferentialGeometry.Topology.loop_arclength_le_of_riemannian_lipschitz

end DifferentialGeometry.Topology
