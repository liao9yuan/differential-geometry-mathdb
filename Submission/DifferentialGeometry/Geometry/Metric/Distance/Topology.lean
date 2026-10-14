import Submission.DifferentialGeometry.Geometry.Metric.Distance.Finiteness
import Mathlib.Topology.Order.Compact

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.SmoothRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RegularSpace M] [PreconnectedSpace M]

@[reducible] def toPseudoMetricSpace (g : SmoothRiemannianMetric I M) : PseudoMetricSpace M :=
  let _ : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let _ : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  PseudoEMetricSpace.toPseudoMetricSpace fun x y => (Manifold.riemannianEDist_lt_top (I := I) x y).ne

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SmoothRiemannianMetric.toPseudoMetricSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SmoothRiemannianMetric.toPseudoMetricSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SmoothRiemannianMetric.toPseudoMetricSpace ``Submission.DifferentialGeometry.SmoothRiemannianMetric.toPseudoMetricSpace

@[simp] theorem toPseudoMetricSpace_toTopologicalSpace (g : SmoothRiemannianMetric I M) :
    g.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace = ‹TopologicalSpace M› := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SmoothRiemannianMetric.toPseudoMetricSpace_toTopologicalSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SmoothRiemannianMetric.toPseudoMetricSpace_toTopologicalSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SmoothRiemannianMetric.toPseudoMetricSpace_toTopologicalSpace ``Submission.DifferentialGeometry.SmoothRiemannianMetric.toPseudoMetricSpace_toTopologicalSpace

theorem toPseudoMetricSpace_edist (g : SmoothRiemannianMetric I M) (x y : M) :
    @_root_.EDist.edist M g.toPseudoMetricSpace.toEDist x y = riemannianEDistOf g x y := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SmoothRiemannianMetric.toPseudoMetricSpace_edist then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SmoothRiemannianMetric.toPseudoMetricSpace_edist"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SmoothRiemannianMetric.toPseudoMetricSpace_edist ``Submission.DifferentialGeometry.SmoothRiemannianMetric.toPseudoMetricSpace_edist

end DifferentialGeometry.SmoothRiemannianMetric

end

noncomputable section

open _root_.Set _root_.Function _root_.Bundle _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.SmoothRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompactSpace M] [T2Space M]

theorem exists_pos_forall_riemannianEDistOf_lt_of_norm_sub_lt
    (g : SmoothRiemannianMetric I M) (e : M → F) (he : _root_.Topology.IsEmbedding e)
    {ρ : ℝ≥0∞} (hρ : 0 < ρ) :
    ∃ δ > 0, ∀ x y : M, ‖e x - e y‖ < δ → riemannianEDistOf g x y < ρ := by
  let : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric I M
  have hdist : ∀ x y : M, riemannianEDistOf g x y = _root_.EDist.edist x y := fun _ _ => rfl
  have hcont : Continuous fun p : M × M => ‖e p.1 - e p.2‖ :=
    ((he.continuous.comp continuous_fst).sub (he.continuous.comp continuous_snd)).norm
  have hclosed : IsClosed {p : M × M | ρ ≤ _root_.EDist.edist p.1 p.2} :=
    isClosed_le continuous_const (continuous_fst.edist continuous_snd)
  obtain ⟨δ, hδpos, hδ⟩ := hclosed.isCompact.exists_forall_le' hcont.continuousOn
    (a := (0 : ℝ)) fun p hp => by
      rcases eq_or_lt_of_le (norm_nonneg (e p.1 - e p.2)) with h | h
      · exfalso
        have hz : e p.1 = e p.2 := sub_eq_zero.mp (norm_eq_zero.mp h.symm)
        have hxy : p.1 = p.2 := he.injective hz
        have hp' : ρ ≤ _root_.EDist.edist p.1 p.2 := hp
        rw [hxy, _root_.PseudoEMetricSpace.edist_self] at hp'
        exact absurd hp' (not_le.mpr hρ)
      · exact h
  refine ⟨δ, hδpos, fun x y hxy => ?_⟩
  have hlt : _root_.EDist.edist x y < ρ := by
    by_contra hle
    exact absurd (hδ (x, y) (not_lt.mp hle)) (not_le.mpr hxy)
  simpa only [hdist x y] using hlt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SmoothRiemannianMetric.exists_pos_forall_riemannianEDistOf_lt_of_norm_sub_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SmoothRiemannianMetric.exists_pos_forall_riemannianEDistOf_lt_of_norm_sub_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SmoothRiemannianMetric.exists_pos_forall_riemannianEDistOf_lt_of_norm_sub_lt ``Submission.DifferentialGeometry.SmoothRiemannianMetric.exists_pos_forall_riemannianEDistOf_lt_of_norm_sub_lt


end DifferentialGeometry.SmoothRiemannianMetric
