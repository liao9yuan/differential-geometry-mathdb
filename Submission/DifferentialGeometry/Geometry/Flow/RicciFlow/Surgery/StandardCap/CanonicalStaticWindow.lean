import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckMarkSideBridge
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWitness

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry.Neck
open _root_.Submission.DifferentialGeometry.Geometry.Metric _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Topology.Manifold.Attachment
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealThreeSpaceHAddOfNat : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealThreeSpaceHAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealThreeSpaceHAddOfNat target :: scope.openDecls } }
private local instance quotientChartedSpace {B : ℝ} {hB : 0 < B} :
    ChartedSpace ThreeSpace (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.quotientChartedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.quotientChartedSpace target :: scope.openDecls } }
private local instance quotientIsManifold {B : ℝ} {hB : 0 < B} :
    IsManifold ThreeModel ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.quotientIsManifold
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.quotientIsManifold target :: scope.openDecls } }
private local instance quotientT2Space {B : ℝ} {hB : 0 < B} :
    T2Space (InsertionQuotient hB) := radialCapAttachment_t2Space transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.quotientT2Space
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.quotientT2Space target :: scope.openDecls } }

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
  {d : normalizedDatum g x₀ δ k}
  {A : ℝ} {hA : 0 < A} {D : ℝ} {m : ℕ} {ε : ℝ}

namespace CanonicalStaticInsertionWitness

variable (w : CanonicalStaticInsertionWitness d A hA D m ε)


include w in
theorem accuracy_pos : 0 < ε :=
  ENNReal.ofReal_pos.mp (bot_le.trans_lt w.properties.window_close)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.accuracy_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.accuracy_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.accuracy_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.accuracy_pos

def window : C(standardCapWindow D, InsertionQuotient (inv_pos.mpr d.precision_pos)) :=
  ⟨w.data.windowMap, w.properties.window_embedding.contMDiff.continuous⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.window then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.window"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.window ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.window

theorem window_smooth : _root_.Manifold.IsSmoothEmbedding ThreeModel ThreeModel ∞ w.window :=
  w.properties.window_embedding

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.window_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.window_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.window_smooth ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.window_smooth

theorem window_tip (hx : (0 : ThreeSpace) ∈ standardCapWindow D) :
    w.window ⟨0, hx⟩ = w.data.tip :=
  w.properties.window_pointed

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.window_tip then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.window_tip"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.window_tip ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.window_tip

def windowMetric : SmoothRiemannianMetric ThreeModel (standardCapWindow D) :=
  pullbackMetricOfInjectiveLocalDiffeomorph
    (scaleMetric (metricScalarAt g x₀) d.scalar_pos w.data.outMetric)
    w.data.windowMap w.properties.window_local w.properties.window_embedding.isEmbedding.injective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.windowMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.windowMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.windowMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.windowMetric

theorem window_inner (x : standardCapWindow D) (V W : TangentSpace ThreeModel x) :
    w.windowMetric.inner x V W = metricScalarAt g x₀ *
      w.data.outMetric.inner (w.window x)
        (mfderiv ThreeModel ThreeModel w.window x V)
        (mfderiv ThreeModel ThreeModel w.window x W) := by
  unfold windowMetric
  erw [pullbackMetricOfInjectiveLocalDiffeomorph_inner, scaleMetric_inner]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.window_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.window_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.window_inner ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.window_inner

theorem window_closeness :
    metricDerivNormSupOn {x : standardCapWindow D | ‖x.val‖ < D} m w.windowMetric
      (standardCapMetric.restrictOpen (standardCapWindow D))
      (standardCapMetric.restrictOpen (standardCapWindow D)) < ε := by
  have h := w.properties.window_close
  change metricDerivENormSupOn
    {x : standardCapWindow D | (riemannianEDistOf metric 0 x.val).toReal < D} m
    w.windowMetric (metric.restrictOpen (standardCapWindow D))
      (metric.restrictOpen (standardCapWindow D)) < ENNReal.ofReal ε at h
  simp only [distance_zero] at h
  have hε : 0 < ε := ENNReal.ofReal_pos.mp (bot_le.trans_lt h)
  have hb : BddAbove {r : ℝ | ∃ j : ℕ, j ≤ m ∧ ∃ x : standardCapWindow D,
      x ∈ {x : standardCapWindow D | ‖x.val‖ < D} ∧
      metricDerivNorm j w.windowMetric (metric.restrictOpen (standardCapWindow D))
        (metric.restrictOpen (standardCapWindow D)) x = r} := by
    refine ⟨ε, ?_⟩
    rintro r ⟨j, hj, x, hx, rfl⟩
    exact (metricDerivNorm_lt_of_sup_lt _ _ _ _ _ h hj hx).le
  rw [metricDerivENormSupOn_eq_ofReal_of_bddAbove _ _ _ _ _ hb] at h
  rw [standardCapMetric_eq_metric]
  exact (ENNReal.ofReal_lt_ofReal_iff hε).mp h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.window_closeness then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.window_closeness"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.window_closeness ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.window_closeness

end CanonicalStaticInsertionWitness
end DifferentialGeometry.PDE.RicciFlow.StandardCap
