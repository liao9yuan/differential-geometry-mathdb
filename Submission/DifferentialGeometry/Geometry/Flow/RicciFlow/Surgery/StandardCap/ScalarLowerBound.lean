import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWitness
import Submission.DifferentialGeometry.Geometry.Curvature.OpenEmbeddingPullback
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Scalar
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Curvature.ScalarPerturbation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry.Neck
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Topology.Manifold.Attachment _root_.Submission.DifferentialGeometry.Geometry.Metric
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.E3 target :: scope.openDecls } }
private abbrev Cap := {x : E3 // ‖x‖ ≤ transitionEnd}

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.Cap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.Cap target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instChartedSpaceE3InsertionQuotient {B : ℝ} {hB : 0 < B} : ChartedSpace E3 (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instChartedSpaceE3InsertionQuotient
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instChartedSpaceE3InsertionQuotient target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopInsertionQuotient {B : ℝ} {hB : 0 < B} : IsManifold (𝓡 3) ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopInsertionQuotient
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopInsertionQuotient target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instT2SpaceInsertionQuotient {B : ℝ} {hB : 0 < B} : T2Space (InsertionQuotient hB) :=
  radialCapAttachment_t2Space transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instT2SpaceInsertionQuotient
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instT2SpaceInsertionQuotient target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instSigmaCompactSpaceSubtypeE3MemOpens (U : _root_.TopologicalSpace.Opens E3) : SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) U.isOpen)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instSigmaCompactSpaceSubtypeE3MemOpens
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instSigmaCompactSpaceSubtypeE3MemOpens target :: scope.openDecls } }

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ A D η : ℝ} {k m : ℕ} {hA : 0 < A}

theorem CanonicalStaticInsertionWitness.cap_scalar_eq_modelWindowPullback
    (d : normalizedDatum g x₀ δ k) (w : CanonicalStaticInsertionWitness d A hA D m η)
    {R : ℝ} (hfit : R ≤ transitionEnd + δ⁻¹) (x : Cap) (hx : ‖x.val‖ < R) :
    metricScalarAt w.data.outMetric (w.data.capMap x) = metricScalarAt g x₀ *
      metricScalarAt
        (modelWindowPullback (inv_pos.mpr d.precision_pos) hfit
          (scaleMetric (metricScalarAt g x₀) d.scalar_pos w.data.outMetric)) ⟨x.val, hx⟩ := by
  have hpoint : modelWindowMap (inv_pos.mpr d.precision_pos) hfit ⟨x.val, hx⟩ =
      w.data.capMap x := by
    rw [w.properties.capMap_eq, w.properties.capInclusion_eq]
    exact modelWindowMap_agrees_cap _ _ x hx
  have hs := metricScalarAt_pullbackMetricOfInjectiveLocalDiffeomorph_scale w.data.outMetric
    (modelWindowMap (inv_pos.mpr d.precision_pos) hfit)
    (modelWindowMap_isLocalDiffeomorph _ _)
    (isSmoothEmbedding_modelWindowMap _ _).isEmbedding.injective
    (metricScalarAt g x₀) d.scalar_pos ⟨x.val, hx⟩
  change metricScalarAt (modelWindowPullback _ hfit
    (scaleMetric (metricScalarAt g x₀) d.scalar_pos w.data.outMetric)) ⟨x.val, hx⟩ = _ at hs
  rw [hpoint] at hs
  rw [hs]
  field_simp [d.scalar_pos.ne']

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.cap_scalar_eq_modelWindowPullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.cap_scalar_eq_modelWindowPullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.cap_scalar_eq_modelWindowPullback ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.cap_scalar_eq_modelWindowPullback

end DifferentialGeometry.PDE.RicciFlow.StandardCap

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instChartedSpaceE3InsertionQuotient_1 {B : ℝ} {hB : 0 < B} : ChartedSpace E3 (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instChartedSpaceE3InsertionQuotient_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instChartedSpaceE3InsertionQuotient_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopInsertionQuotient_1 {B : ℝ} {hB : 0 < B} : IsManifold (𝓡 3) ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopInsertionQuotient_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopInsertionQuotient_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instT2SpaceInsertionQuotient_1 {B : ℝ} {hB : 0 < B} : T2Space (InsertionQuotient hB) :=
  radialCapAttachment_t2Space transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instT2SpaceInsertionQuotient_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instT2SpaceInsertionQuotient_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instSigmaCompactSpaceSubtypeE3MemOpens_1 (U : _root_.TopologicalSpace.Opens E3) : SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) U.isOpen)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instSigmaCompactSpaceSubtypeE3MemOpens_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instSigmaCompactSpaceSubtypeE3MemOpens_1 target :: scope.openDecls } }

theorem exists_canonicalStaticInsertionWitness_cap_scalar_lower_bound (A : ℝ) (hA : 0 < A) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 / 2 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ k : ℕ, 2 ≤ k →
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M],
      ∀ (g : SmoothRiemannianMetric I M) (x₀ : M) (d : normalizedDatum g x₀ δ k)
        (D : ℝ) (m : ℕ) (η : ℝ) (w : CanonicalStaticInsertionWitness d A hA D m η),
        ∀ x ∈ _root_.Set.range w.data.capMap,
          metricScalarAt g x₀ / 2 ≤ metricScalarAt w.data.outMetric x := by
  let U := modelWindow (transitionEnd + 1 + 1)
  let K : Set U := {x | ‖x.val‖ ≤ transitionEnd}
  have hK : IsCompact K := by
    have hcompact : IsCompact {x : E3 | ‖x‖ ≤ transitionEnd} := by
      simpa only [Metric.closedBall, dist_zero_right] using
        _root_.ProperSpace.isCompact_closedBall (0 : E3) transitionEnd
    let j : {x : E3 // ‖x‖ ≤ transitionEnd} → U := fun x =>
      ⟨x.val, by change ‖x.val‖ < transitionEnd + 1 + 1; linarith [x.property]⟩
    have hj : Continuous j := continuous_subtype_val.subtype_mk _
    have himage : _root_.Set.range j = K := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact y.property
      · intro hx
        exact ⟨⟨x.val, hx⟩, Subtype.ext rfl⟩
    rw [← himage]
    let : CompactSpace {x : E3 // ‖x‖ ≤ transitionEnd} := isCompact_iff_compactSpace.mp hcompact
    exact isCompact_range hj
  have hlower : ∀ x ∈ K, 1 ≤ metricScalarAt (metric.restrictOpen U) x := by
    intro x _
    rw [metricScalarAt_restrictOpen]
    exact one_le_metricScalarAt x.val
  obtain ⟨ε, hε, hstable⟩ :=
    exists_scalar_lower_bound_of_small_metric_derivatives (metric.restrictOpen U) hK
      (by norm_num : (0 : ℝ) < 1) hlower
  obtain ⟨δ₀, hδ₀, hhalf, hwindow⟩ := exists_normalizedDatum_modelWindow_error_lt
    A hA (transitionEnd + 1) (by linarith [transitionEnd_pos]) 2 ε hε
  refine ⟨δ₀, hδ₀, hhalf, ?_⟩
  intro δ hδ hle k hk E H M _ _ _ _ _ I _ _ _ _ _ g x₀ d D m η w x hx
  obtain ⟨hAB, hfit, hclose⟩ := hwindow δ hδ hle
  let out := modelWindowPullback (inv_pos.mpr d.precision_pos) hfit
    (scaleMetric (metricScalarAt g x₀) d.scalar_pos w.data.outMetric)
  have hnorm := hclose k hk g x₀ d.oriented
  rw [← w.properties.outMetric_eq] at hnorm
  have hnorm' : ∀ y ∈ K, ∀ j : ℕ, j ≤ 2 →
      metricDerivNorm j out (metric.restrictOpen U) (metric.restrictOpen U) y ≤ ε := by
    intro y hy j hj
    apply (metricDerivNorm_lt_of_sup_lt _ 2 out (metric.restrictOpen U)
      (metric.restrictOpen U) hnorm hj ?_).le
    change (riemannianEDistOf metric 0 y.val).toReal < transitionEnd + 1
    rw [distance_zero]
    exact lt_of_le_of_lt hy (lt_add_one _)
  obtain ⟨z, rfl⟩ := hx
  have hzin : ‖z.val‖ < transitionEnd + 1 + 1 := by linarith [z.property]
  have hz : (⟨z.val, hzin⟩ : U) ∈ K := z.property
  have hscalar := hstable out hnorm' _ hz
  rw [w.cap_scalar_eq_modelWindowPullback d hfit z hzin]
  have hh := mul_le_mul_of_nonneg_left hscalar d.scalar_pos.le
  simpa only [out, div_eq_mul_inv, one_mul] using hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_canonicalStaticInsertionWitness_cap_scalar_lower_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_canonicalStaticInsertionWitness_cap_scalar_lower_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_canonicalStaticInsertionWitness_cap_scalar_lower_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_canonicalStaticInsertionWitness_cap_scalar_lower_bound

end DifferentialGeometry.PDE.RicciFlow.StandardCap
