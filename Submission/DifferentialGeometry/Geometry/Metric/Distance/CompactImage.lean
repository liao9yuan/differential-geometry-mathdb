import Submission.DifferentialGeometry.Topology.EMetricSpace.CompactImage
import Submission.DifferentialGeometry.Geometry.Metric.Distance.Basic
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.LoopSpace.Basic
import Mathlib.Geometry.Manifold.Riemannian.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false

noncomputable section

open _root_.Set
open scoped _root_.ENNReal _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry

open _root_.Bundle
open scoped _root_.Bundle

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [RegularSpace M]

theorem exists_uniform_riemannianEDistOf_bound_of_compact_preconnected
    {A : Type*} [TopologicalSpace A] [CompactSpace A] [PreconnectedSpace A]
    (g : SmoothRiemannianMetric I M) (f : C(A, M)) (a : A) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ b : A,
      riemannianEDistOf g (f b) (f a) ≤ ENNReal.ofReal R := by
  let : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞)
    (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  let : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  exact EMetric.exists_uniform_edist_bound_of_compact_preconnected f.continuous a

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.exists_uniform_riemannianEDistOf_bound_of_compact_preconnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.exists_uniform_riemannianEDistOf_bound_of_compact_preconnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.exists_uniform_riemannianEDistOf_bound_of_compact_preconnected ``Submission.DifferentialGeometry.exists_uniform_riemannianEDistOf_bound_of_compact_preconnected

theorem exists_uniform_riemannianEDistOf_bound_on_loop
    (g : SmoothRiemannianMetric I M) (γ : Topology.freeLoop M) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ θ : Topology.loopCircle,
      riemannianEDistOf g (γ θ) (γ 0) ≤ ENNReal.ofReal R :=
  exists_uniform_riemannianEDistOf_bound_of_compact_preconnected g γ 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.exists_uniform_riemannianEDistOf_bound_on_loop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.exists_uniform_riemannianEDistOf_bound_on_loop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.exists_uniform_riemannianEDistOf_bound_on_loop ``Submission.DifferentialGeometry.exists_uniform_riemannianEDistOf_bound_on_loop

end DifferentialGeometry

end

end
