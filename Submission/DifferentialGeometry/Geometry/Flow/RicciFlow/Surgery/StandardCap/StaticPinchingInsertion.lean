import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWitness

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.TopologicalSpace _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Riemannian _root_.Submission.DifferentialGeometry.Topology
open _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Geometry.Metric _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Topology.Manifold.Attachment _root_.Submission.DifferentialGeometry.Topology.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Topology.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal
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
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instNeZeroNatFinrankRealE3 : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instNeZeroNatFinrankRealE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instNeZeroNatFinrankRealE3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instChartedSpaceEuclideanHalfSpaceOfNatNatCap : ChartedSpace (EuclideanHalfSpace 3) Cap := closedBallChartedSpace transitionEnd_pos

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instChartedSpaceEuclideanHalfSpaceOfNatNatCap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instChartedSpaceEuclideanHalfSpaceOfNatNatCap target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instIsManifoldRealEuclideanSpaceFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopCap : IsManifold (𝓡∂ 3) ∞ Cap := closedBall_isManifold transitionEnd_pos

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instIsManifoldRealEuclideanSpaceFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopCap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instIsManifoldRealEuclideanSpaceFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopCap target :: scope.openDecls } }
private local instance quotientChartedSpace {B : ℝ} {hB : 0 < B} :
    ChartedSpace E3 (InsertionQuotient hB) := radialCapAttachmentChartedSpace transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.quotientChartedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.quotientChartedSpace target :: scope.openDecls } }
private local instance quotientIsManifold {B : ℝ} {hB : 0 < B} :
    IsManifold (𝓡 3) ∞ (InsertionQuotient hB) := radialCapAttachment_isManifold transitionEnd_pos hB

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

structure StaticInsertionAdditionalProperties (C : ℕ → ℝ)
    {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {D : ℝ} {m : ℕ} {ε : ℝ}
    (w : CanonicalStaticInsertionWitness d A hA D m ε) : Prop where
  deep_metric : ∀ (x : Cap), x.val ∈ deepRegion A → ∀ v u : TangentSpace (𝓡∂ 3) x,
    (scaleMetric (metricScalarAt g x₀) d.scalar_pos w.data.outMetric).inner (w.data.capMap x)
      (mfderiv (𝓡∂ 3) (𝓡 3) w.data.capMap x v) (mfderiv (𝓡∂ 3) (𝓡 3) w.data.capMap x u) =
    (1 - Real.sqrt δ) * metric.inner x.val
      (mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : Cap → E3) x v)
      (mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : Cap → E3) x u)
  positive_region : ∀ (x : Cap), x.val ∈ positiveRegion A →
    ∀ u v : TangentSpace (𝓡 3) (w.data.capMap x),
      w.data.outMetric.inner (w.data.capMap x) u u * w.data.outMetric.inner (w.data.capMap x) v v -
        w.data.outMetric.inner (w.data.capMap x) u v ^ 2 ≠ 0 →
      0 < sectionalCurvature w.data.outMetric (w.data.capMap x) u v
  hamiltonIvey : ∀ a : ℝ, 0 < a →
    (∀ q : openCylinder δ⁻¹,
      (metricScalarAt g (d.controlledMap q),
        2 * leastCurvatureOperatorEigenvalueAt g (d.controlledMap q)
          (metricAlgebraicCurvatureTensorAt g (d.controlledMap q))) ∈ fixedHamiltonIveyRegion a) →
    ∀ x, (metricScalarAt w.data.outMetric x,
      2 * leastCurvatureOperatorEigenvalueAt w.data.outMetric x
        (metricAlgebraicCurvatureTensorAt w.data.outMetric x)) ∈ fixedHamiltonIveyRegion a
  scalar_floor : ∀ L₀ : ℝ, L₀ ≤ 0 →
    (∀ q : openCylinder δ⁻¹, L₀ ≤ metricScalarAt g (d.controlledMap q)) →
    ∀ x, L₀ ≤ metricScalarAt w.data.outMetric x
  scalar_positive : ∀ x, 0 < metricScalarAt w.data.outMetric x
  cap_derivatives : ∀ x ∈ _root_.Set.range w.data.capMap, ∀ j ≤ m,
    Real.sqrt (normSq0S w.data.outMetric x (4 + j) (iterCov w.data.outMetric 4 (metricRm04 w.data.outMetric) j x)) ≤
      C j * (metricScalarAt g x₀) ^ (1 + (j : ℝ) / 2)
  cap_scalar : ∀ x ∈ _root_.Set.range w.data.capMap,
    0 < metricScalarAt w.data.outMetric x ∧ metricScalarAt w.data.outMetric x ≤ C 0 * metricScalarAt g x₀

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.StaticInsertionAdditionalProperties then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.StaticInsertionAdditionalProperties"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.StaticInsertionAdditionalProperties ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.StaticInsertionAdditionalProperties

theorem exists_staticInsertion_with_additional_properties :
    ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧ ∃ (A : ℝ) (hA : 0 < A), 2 * A < 1 / 2 ∧
      ∀ (D : ℝ), 0 < D → ∀ (m : ℕ) (ε : ℝ), 0 < ε →
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 / 2 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M],
        ∀ (g : SmoothRiemannianMetric I M) (x₀ : M) (d : normalizedDatum g x₀ δ (m + 4)),
          ∃ w : CanonicalStaticInsertionWitness d A hA D m ε,
            StaticInsertionAdditionalProperties C w := by
  obtain ⟨C, hC, A, hA, hsmall, hmod⟩ := exists_uniform_positiveCoordinate_static_estimates
  refine ⟨C, hC, A, hA, hsmall, ?_⟩
  intro D hD m ε hε
  obtain ⟨δ₀, hδ₀, hhalf, hb⟩ := hmod D hD m ε hε
  refine ⟨δ₀, hδ₀, hhalf, ?_⟩
  intro δ hδ hle
  obtain ⟨hAB, hfit, htip, hbound⟩ := hb δ hδ hle
  intro E H M _ _ _ _ _ I _ _ _ _ _ g x₀ d
  obtain ⟨hclose, hR, hHI, hder⟩ := hbound g x₀ d.oriented
  let w := canonicalStaticInsertionWitness d A hA D hD m ε hAB hfit htip hclose
  refine ⟨w, ?_⟩
  refine
    { deep_metric := normalizedDatum_positiveSideInsertionMetric_fixed_deep d.oriented hA hAB
      positive_region := ?_
      hamiltonIvey := ?_
      scalar_floor := fun L₀ hL₀ _ x => hL₀.trans (hR x).le
      scalar_positive := hR
      cap_derivatives := fun x hx => (hder x hx).1
      cap_scalar := fun x hx => ⟨hR x, (le_abs_self _).trans (hder x hx).2⟩ }
  · intro x hx u v hplane
    have he := normalizedDatum_positiveSideInsertionMetric_fixed_positive_sectional d.oriented hA hAB x hx u v hplane
    exact (div_pos d.scalar_pos
      (mul_pos (by norm_num) d.oriented.controlledMetric_cylinder_lower.1)).trans_eq he.symm
  · intro a ha hin
    apply hHI a ha
    intro q
    have he := d.oriented_controlledMap q
    rw [he]
    exact hin _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_staticInsertion_with_additional_properties then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_staticInsertion_with_additional_properties"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_staticInsertion_with_additional_properties ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_staticInsertion_with_additional_properties
end DifferentialGeometry.PDE.RicciFlow.StandardCap
