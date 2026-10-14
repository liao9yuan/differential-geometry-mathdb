import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CanonicalRetainedMetric
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CanonicalCapChart
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CanonicalStaticCollapseLength
import Submission.DifferentialGeometry.Geometry.Metric.RestrictionDistance

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.Manifold _root_.Submission.Manifold _root_.Filter
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry.Neck
open _root_.Submission.DifferentialGeometry.Topology.Manifold _root_.Submission.DifferentialGeometry.Topology.Manifold.Attachment
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.E3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }
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

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
  {d : normalizedDatum g x₀ δ k}
  {A : ℝ} {hA : 0 < A} {D : ℝ} {m : ℕ} {ε : ℝ}

private def centralOpenMap (δ : ℝ) : C(neckCentralDomain δ, openCylinder δ⁻¹) :=
  ⟨fun q => ⟨q.1.1, q.2⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.centralOpenMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.centralOpenMap target :: scope.openDecls } }

private def centralImageMap (d : normalizedDatum g x₀ δ k) :
    C(neckCentralDomain δ, d.oriented.controlledImage) :=
  ⟨fun q => ⟨d.oriented.controlledMap (centralOpenMap δ q),
    d.oriented.controlledMap_mem_controlledImage _⟩,
    (d.oriented.controlledMap_smooth.continuous.comp (centralOpenMap δ).continuous).subtype_mk _⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.centralImageMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.centralImageMap target :: scope.openDecls } }

namespace CanonicalStaticInsertionWitness

variable (w : CanonicalStaticInsertionWitness d A hA D m ε)

def collapse : C(neckCentralDomain δ, InsertionQuotient (inv_pos.mpr d.precision_pos)) :=
  ⟨w.data.collapse ∘ centralImageMap d, by
    have h : Continuous w.data.collapse := by
      rw [w.properties.collapse_eq]
      exact d.oriented.continuous_positiveSideQuotientCollapseMap hA w.properties.cut_fit
    exact h.comp (centralImageMap d).continuous⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.collapse then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.collapse"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.collapse ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.collapse

theorem collapse_retained (x : neckCentralDomain δ) (hz : 0 ≤ x.1.1.2) :
    w.collapse x = w.retainedMap ⟨x.1.1, hz, x.2.2⟩ := by
  exact w.properties.collapse_retained (x.1.1.1, ⟨x.1.1.2, hz, x.2.2⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.collapse_retained then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.collapse_retained"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.collapse_retained ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.collapse_retained

theorem collapse_tip (x : neckCentralDomain δ) (hz : x.1.1.2 ≤ w.data.profileTip) :
    w.collapse x = w.data.tip :=
  w.properties.collapse_collapsed (centralOpenMap δ x) hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.collapse_tip then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.collapse_tip"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.collapse_tip ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.collapse_tip

theorem collapse_radial (x : neckCentralDomain δ)
    (hlo : w.data.profileTip < x.1.1.2) (hhi : x.1.1.2 ≤ 0)
    (hx : w.data.profile x.1.1.2 • x.1.1.1.1 ∈ standardCapClosedCore) :
    w.collapse x = w.capChart ⟨w.data.profile x.1.1.2 • x.1.1.1.1, hx⟩ := by
  exact w.properties.collapse_radial (centralOpenMap δ x) ⟨hlo.le, hhi⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.collapse_radial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.collapse_radial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.collapse_radial ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.collapse_radial

theorem collapse_length (γ : ℝ → neckCentralDomain δ) (a b : ℝ)
    (hγ : ContinuousOn γ (_root_.Set.Icc a b)) :
    riemannianCurveLength w.data.outMetric (w.collapse ∘ γ) a b ≤
      riemannianCurveLength g (fun t => d.oriented.map (γ t).1) a b := by
  exact w.collapse_length_of_toNormalizedNeck γ a b hγ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.collapse_length then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.collapse_length"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.collapse_length ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.collapse_length

theorem collapse_locallyLipschitz (x : neckCentralDomain δ) :
    ∃ U ∈ 𝓝 x, ∃ L : ℝ≥0, ∀ y ∈ U, ∀ z ∈ U,
      riemannianEDistOf w.data.outMetric (w.collapse y) (w.collapse z) ≤
        L * riemannianEDistOf g (d.oriented.map y.1) (d.oriented.map z.1) := by
  let : RegularSpace M := DifferentialGeometry.Topology.Manifold.regularSpace_of_chartedSpace I
  obtain ⟨L, V, hV, hL⟩ := w.properties.collapse_locallyLipschitz (centralImageMap d x)
  obtain ⟨W, hW, hdist⟩ :=
    DifferentialGeometry.Geometry.Metric.exists_mem_nhds_riemannianEDistOf_restrictOpen_eq
      g d.oriented.controlledImage (centralImageMap d x)
  refine ⟨(centralImageMap d) ⁻¹' V ∩
      (fun y => (centralImageMap d y).val) ⁻¹' W, ?_, L, ?_⟩
  · exact _root_.Filter.inter_mem ((centralImageMap d).continuous.continuousAt.preimage_mem_nhds hV)
      ((continuous_subtype_val.comp
        (centralImageMap d).continuous).continuousAt.preimage_mem_nhds hW)
  · intro y hy z hz
    have h := hL (centralImageMap d y) hy.1 (centralImageMap d z) hz.1
    rw [hdist (centralImageMap d y) (centralImageMap d z) hy.2 hz.2] at h
    exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.collapse_locallyLipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.collapse_locallyLipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.collapse_locallyLipschitz ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.collapse_locallyLipschitz

end CanonicalStaticInsertionWitness
end DifferentialGeometry.PDE.RicciFlow.StandardCap
