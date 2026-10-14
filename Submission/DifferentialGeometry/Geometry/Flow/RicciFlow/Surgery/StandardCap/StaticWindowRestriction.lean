import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWitnessTransport
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CanonicalStaticWindow

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Manifold _root_.Submission.Manifold _root_.TopologicalSpace _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Geometry.Metric
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Topology.Manifold.Attachment
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

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
    IsManifold (𝓡 3) ∞ (InsertionQuotient hB) :=
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
  {A : ℝ} {hA : 0 < A} {D D' : ℝ} {m : ℕ} {ε : ℝ}

namespace CanonicalStaticInsertionWitness

variable (w : CanonicalStaticInsertionWitness d A hA D m ε)

private theorem canonical_window_close_restrict (hD'D : D' ≤ D) :
    metricDerivENormSupOn
      {x : modelWindow (D' + 1) | (riemannianEDistOf metric 0 x.val).toReal < D'} m
      (modelWindowPullback (inv_pos.mpr d.precision_pos)
        ((add_le_add hD'D (le_refl 1)).trans w.properties.window_fit)
        (scaleMetric (metricScalarAt g x₀) d.scalar_pos
          (d.oriented.positiveSideInsertionMetric hA w.properties.cut_fit)))
      (metric.restrictOpen (modelWindow (D' + 1)))
      (metric.restrictOpen (modelWindow (D' + 1))) < ENNReal.ofReal ε := by
  have hclose := w.canonical_window_close
  rw [normalizedDatum_modelWindowPullback] at hclose ⊢
  refine lt_of_le_of_lt ?_ hclose
  apply (metricDerivENormSupOn_le_iff _ _ _ _ _ _).mpr
  intro j hj x hx
  let y : modelWindow (D + 1) := ⟨x.val, x.property.trans_le (add_le_add hD'D (le_refl 1))⟩
  have hy : (riemannianEDistOf metric 0 y.val).toReal < D := hx.trans_le hD'D
  let G := insertedMetric hA w.properties.cut_fit
    d.oriented.controlledMetric_cylinder_lower.1 d.oriented.controlledMetric
  let U := insertionBall δ⁻¹
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen (𝓡 3) U.isOpen)
  have hn := metricDerivNorm_flat
    (modelWindow_le_insertionBall ((add_le_add hD'D (le_refl 1)).trans w.properties.window_fit))
    G (metric.restrictOpen U) (metric.restrictOpen U) j x
  have hn' := metricDerivNorm_flat
    (modelWindow_le_insertionBall w.properties.window_fit)
    G (metric.restrictOpen U) (metric.restrictOpen U) j y
  rw [SmoothRiemannianMetric.restrictOpen_flat] at hn hn'
  rw [hn, ← hn']
  exact ofReal_metricDerivNorm_le_sup _ m _ _ _ hj hy

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.canonical_window_close_restrict
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.canonical_window_close_restrict target :: scope.openDecls } }

def restrictWindow (hD' : 0 < D') (hD'D : D' ≤ D) :
    CanonicalStaticInsertionWitness d A hA D' m ε := by
  apply canonicalStaticInsertionWitness d A hA D' hD' m ε
    w.properties.cut_fit ((add_le_add hD'D (le_refl 1)).trans w.properties.window_fit)
  · exact w.properties.profileTip_eq ▸ w.properties.profileTip_location
  · exact w.canonical_window_close_restrict hD'D

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow

@[simp] theorem restrictWindow_quotientDiffeomorph (hD' : 0 < D') (hD'D : D' ≤ D) :
    (w.restrictWindow hD' hD'D).data.quotientDiffeomorph = w.data.quotientDiffeomorph :=
  (w.restrictWindow hD' hD'D).properties.quotientDiffeomorph_eq.trans
    w.properties.quotientDiffeomorph_eq.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_quotientDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_quotientDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_quotientDiffeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_quotientDiffeomorph

@[simp] theorem restrictWindow_gluingDiffeomorph (hD' : 0 < D') (hD'D : D' ≤ D) :
    (w.restrictWindow hD' hD'D).data.gluingDiffeomorph = w.data.gluingDiffeomorph :=
  (w.restrictWindow hD' hD'D).properties.gluingDiffeomorph_eq.trans
    w.properties.gluingDiffeomorph_eq.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_gluingDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_gluingDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_gluingDiffeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_gluingDiffeomorph

@[simp] theorem restrictWindow_profileTip (hD' : 0 < D') (hD'D : D' ≤ D) :
    (w.restrictWindow hD' hD'D).data.profileTip = w.data.profileTip :=
  (w.restrictWindow hD' hD'D).properties.profileTip_eq.trans w.properties.profileTip_eq.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_profileTip then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_profileTip"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_profileTip ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_profileTip

@[simp] theorem restrictWindow_profile (hD' : 0 < D') (hD'D : D' ≤ D) :
    (w.restrictWindow hD' hD'D).data.profile = w.data.profile :=
  (w.restrictWindow hD' hD'D).properties.profile_eq.trans w.properties.profile_eq.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_profile then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_profile"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_profile ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_profile

@[simp] theorem restrictWindow_outMetric (hD' : 0 < D') (hD'D : D' ≤ D) :
    (w.restrictWindow hD' hD'D).data.outMetric = w.data.outMetric :=
  (w.restrictWindow hD' hD'D).properties.outMetric_eq.trans w.properties.outMetric_eq.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_outMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_outMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_outMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_outMetric

@[simp] theorem restrictWindow_capInclusion (hD' : 0 < D') (hD'D : D' ≤ D) :
    (w.restrictWindow hD' hD'D).data.capInclusion = w.data.capInclusion :=
  (w.restrictWindow hD' hD'D).properties.capInclusion_eq.trans
    w.properties.capInclusion_eq.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_capInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_capInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_capInclusion ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_capInclusion

@[simp] theorem restrictWindow_retainedInclusion (hD' : 0 < D') (hD'D : D' ≤ D) :
    (w.restrictWindow hD' hD'D).data.retainedInclusion = w.data.retainedInclusion :=
  (w.restrictWindow hD' hD'D).properties.retainedInclusion_eq.trans
    w.properties.retainedInclusion_eq.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_retainedInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_retainedInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_retainedInclusion ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_retainedInclusion

@[simp] theorem restrictWindow_capMap (hD' : 0 < D') (hD'D : D' ≤ D) :
    (w.restrictWindow hD' hD'D).data.capMap = w.data.capMap := by
  rw [(w.restrictWindow hD' hD'D).properties.capMap_eq,
    w.properties.capMap_eq, restrictWindow_capInclusion]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_capMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_capMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_capMap ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_capMap

@[simp] theorem restrictWindow_deepMap (hD' : 0 < D') (hD'D : D' ≤ D) :
    (w.restrictWindow hD' hD'D).data.deepMap = w.data.deepMap := by
  rw [(w.restrictWindow hD' hD'D).properties.deepMap_eq,
    w.properties.deepMap_eq, restrictWindow_capMap]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_deepMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_deepMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_deepMap ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_deepMap

@[simp] theorem restrictWindow_tip (hD' : 0 < D') (hD'D : D' ≤ D) :
    (w.restrictWindow hD' hD'D).data.tip = w.data.tip := by
  rw [(w.restrictWindow hD' hD'D).properties.tip_eq,
    w.properties.tip_eq, restrictWindow_capInclusion]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_tip then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_tip"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_tip ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_tip

@[simp] theorem restrictWindow_collapse (hD' : 0 < D') (hD'D : D' ≤ D) :
    (w.restrictWindow hD' hD'D).data.collapse = w.data.collapse :=
  (w.restrictWindow hD' hD'D).properties.collapse_eq.trans w.properties.collapse_eq.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_collapse then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_collapse"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_collapse ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_collapse

@[simp] theorem restrictWindow_window (hD' : 0 < D') (hD'D : D' ≤ D)
    (x : standardCapWindow D') :
    (w.restrictWindow hD' hD'D).window x =
      w.window ⟨x.val, x.property.trans_le (add_le_add hD'D (le_refl 1))⟩ := by
  change (w.restrictWindow hD' hD'D).data.windowMap x = w.data.windowMap _
  rw [(w.restrictWindow hD' hD'D).properties.windowMap_eq, w.properties.windowMap_eq]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_window then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_window"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_window ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_window

@[simp] theorem restrictWindow_windowMetric (hD' : 0 < D') (hD'D : D' ≤ D) :
    (w.restrictWindow hD' hD'D).windowMetric =
      w.windowMetric.restrictOpenOfSubset
        (fun _ hx => hx.trans_le (add_le_add hD'D (le_refl 1)) :
          standardCapWindow D' ≤ standardCapWindow D) := by
  simp only [windowMetric, (w.restrictWindow hD' hD'D).properties.windowMap_eq,
    restrictWindow_outMetric, w.properties.windowMap_eq]
  exact modelWindowPullback_restrict (inv_pos.mpr d.precision_pos)
    (add_le_add hD'D (le_refl 1)) w.properties.window_fit _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_windowMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_windowMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_windowMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_windowMetric

end CanonicalStaticInsertionWitness
end DifferentialGeometry.PDE.RicciFlow.StandardCap
