import Submission.DifferentialGeometry.Topology.LoopSpace.RegularTopology
import Submission.DifferentialGeometry.Topology.LoopSpace.Lipschitz
import Submission.DifferentialGeometry.Geometry.Metric.CompactSourceCurves
import Mathlib.Analysis.Calculus.MeanValue

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.ContinuousMap _root_.Manifold _root_.Submission.Manifold _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry
open scoped _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Bundle _root_.Submission.Bundle _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Topology

variable {K E F : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M] [Nonempty M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_regular_family_lipschitz_bound (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (e : M → F) (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, _root_.Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e p))
    (Γ : K → regularLoop E M)
    (hΓ : Continuous[inferInstance, regularLoopTopology e (he.of_le (by exact_mod_cast le_top))] Γ) :
    ∃ V : ℝ≥0, ∀ k θ η,
      riemannianEDistOf g ((Γ k).val θ) ((Γ k).val η) ≤ (V : ℝ≥0∞) * _root_.EDist.edist θ η := by
  let he₁ := he.of_le (show (1 : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) by exact_mod_cast le_top)
  have hjet : Continuous (fun k => regularLoopJet e he₁ (Γ k)) := continuous_induced_rng.mp hΓ
  have hD : Continuous (fun p : K × loopCircle => regularLoopDerivative e he₁ (Γ p.1) p.2) :=
    (FreeLoop.continuous_family_iff _).mp hjet.snd
  obtain ⟨B, hB⟩ := (isCompact_range hD).isBounded.exists_norm_le
  let D : ℝ≥0 := ⟨max B 0, le_max_right _ _⟩
  have hDbound (k : K) (t : ℝ) : ‖deriv (fun s : ℝ => e ((Γ k).val (s : loopCircle))) t‖ ≤ D :=
    (hB _ (_root_.Set.mem_range_self (k, (t : loopCircle)))).trans (le_max_left _ _)
  have hLip (k : K) : LipschitzWith D (fun t : ℝ => e ((Γ k).val (t : loopCircle))) := by
    apply lipschitzWith_of_nnnorm_deriv_le
      ((regularLoop_embedded_contDiff e he₁ (Γ k)).differentiable one_ne_zero)
    intro t
    exact_mod_cast hDbound k t
  obtain ⟨r, U, hU, heU, hr, hleft⟩ :=
    DifferentialGeometry.Geometry.exists_smooth_neighborhood_retraction he hemb hi
  obtain ⟨Cr, hCr⟩ := DifferentialGeometry.Geometry.exists_compact_source_curve_lipschitz g hU
    (hr.of_le (by exact_mod_cast le_top)) (isCompact_range he.continuous) heU
  let cg := g.toContinuousRiemannianMetric
  let : _root_.Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨cg.toRiemannianMetric⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  refine ⟨Cr * D, fun k θ η => ?_⟩
  have hLift : LipschitzWith (Cr * D) (fun t : ℝ => (Γ k).val (t : loopCircle)) := by
    intro x y
    have h := hCr D (fun t : ℝ => e ((Γ k).val (t : loopCircle)))
      (regularLoop_embedded_contDiff e he₁ (Γ k)) (hLip k) (fun t => _root_.Set.mem_range_self _) x y
    simpa only [hleft] using! h
  exact (loop_lipschitz_of_lift (γ := (Γ k).val) hLift).edist_le_mul θ η

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_regular_family_lipschitz_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_regular_family_lipschitz_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_regular_family_lipschitz_bound ``Submission.DifferentialGeometry.Topology.exists_regular_family_lipschitz_bound

end DifferentialGeometry.Topology
