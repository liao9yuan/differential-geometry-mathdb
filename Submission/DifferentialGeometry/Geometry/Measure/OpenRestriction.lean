import Submission.DifferentialGeometry.Analysis.Integration.Measure.Parametric.Evaluation
import Submission.DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.OpenSubtype
import Submission.DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Manifold _root_.MeasureTheory _root_.Bundle _root_.TopologicalSpace
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold _root_.ContDiff _root_.ENNReal _root_.Topology
namespace DifferentialGeometry.Geometry.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
private local instance _root_.Submission.DifferentialGeometry.Geometry.Measure.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Measure.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Measure.instLocallyCompactSpaceSubtypeMemOpens_differentialGeometry (U : _root_.TopologicalSpace.Opens E) : LocallyCompactSpace U := U.isOpen.locallyCompactSpace

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.instLocallyCompactSpaceSubtypeMemOpens_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.instLocallyCompactSpaceSubtypeMemOpens_differentialGeometry target :: scope.openDecls } }

private def openParam (U : _root_.TopologicalSpace.Opens E) (x : U) : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E U 1 where
  toPartialEquiv := (chartAt E x).symm.toPartialEquiv
  open_source := (chartAt E x).open_target
  open_target := (chartAt E x).open_source
  contMDiffOn_toFun := contMDiffOn_chart_symm
  contMDiffOn_invFun := contMDiffOn_chart

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.openParam
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.openParam target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private theorem openParam_source (U : _root_.TopologicalSpace.Opens E) (x : U) : (openParam U x).source = U := by
  change ((OpenPartialHomeomorph.refl E).subtypeRestr (s := U) ⟨x⟩).target = U
  rw [OpenPartialHomeomorph.subtypeRestr_def, OpenPartialHomeomorph.trans_refl,
    Opens.openPartialHomeomorphSubtypeCoe_target]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.openParam_source
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.openParam_source target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private theorem openParam_val (U : _root_.TopologicalSpace.Opens E) (x : U) {w : E} (hw : w ∈ U) :
    (openParam U x w).val = w := by
  have ht : w ∈ ((OpenPartialHomeomorph.refl E).subtypeRestr (s := U) ⟨x⟩).target :=
    by change w ∈ (openParam U x).source; rwa [openParam_source]
  exact (OpenPartialHomeomorph.refl E).subtypeRestr_symm_apply ⟨x⟩ ht

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.openParam_val
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.openParam_val target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private theorem openParam_mfderiv (U : _root_.TopologicalSpace.Opens E) (x : U) {w : E} (hw : w ∈ U) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (openParam U x) w = ContinuousLinearMap.id ℝ E := by
  have hp : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (openParam U x) w :=
    (openParam U x).mdifferentiableAt (by norm_num) ((openParam_source U x).symm ▸ hw)
  have he : (Subtype.val ∘ openParam U x : E → E) =ᶠ[𝓝 w] id :=
    Filter.eventuallyEq_of_mem (U.isOpen.mem_nhds hw) (fun y hy => openParam_val U x hy)
  have hd := he.mfderiv_eq (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E))
  rw [mfderiv_comp w (hasMFDerivAt_subtype_val U _).mdifferentiableAt hp,
    mfderiv_subtype_val, mfderiv_id] at hd
  exact hd

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.openParam_mfderiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.openParam_mfderiv target :: scope.openDecls } }

private def identityParam : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E 1 :=
  (Diffeomorph.refl 𝓘(ℝ, E) E 1).toPartialDiffeomorph

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.identityParam
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.identityParam target :: scope.openDecls } }

private theorem openParam_density (g : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (U : _root_.TopologicalSpace.Opens E) (x : U) {w : E} (hw : w ∈ U) :
    paramDensity (g.restrictOpen U) (openParam U x) w = paramDensity g identityParam w := by
  rw [paramDensity_apply, paramDensity_apply]
  congr 2
  ext i j
  simp only [paramGramMatrix_apply, SmoothRiemannianMetric.restrictOpen_inner]
  erw [openParam_mfderiv U x hw, openParam_val U x hw]
  change g.inner w ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) =
    g.inner w (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) id w ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) id w ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j))
  rw [mfderiv_id]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.openParam_density
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.openParam_density target :: scope.openDecls } }

theorem riemannianVolumeMeasure_restrictOpen_preimage
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) E) (U : _root_.TopologicalSpace.Opens E)
    {K : Set E} (hK : MeasurableSet K) (hKU : K ⊆ U) :
    riemannianVolumeMeasure 𝓘(ℝ, E) U (g.restrictOpen U) (Subtype.val ⁻¹' K) =
      riemannianVolumeMeasure 𝓘(ℝ, E) E g K := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp only [_root_.Set.preimage_empty, _root_.MeasureTheory.measure_empty]
  let xU : U := ⟨x, hKU hx⟩
  have himage : (openParam U xU) '' K = Subtype.val ⁻¹' K := by
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      change (openParam U xU w).val ∈ K
      rwa [openParam_val U xU (hKU hw)]
    · intro hy
      refine ⟨y.val, hy, Subtype.ext ?_⟩
      exact openParam_val U xU y.property
  rw [← himage, riemannianVolumeMeasure_image_param_eq (g.restrictOpen U) (openParam U xU)
    hK (by simpa only [openParam_source] using hKU)]
  have hid := riemannianVolumeMeasure_image_param_eq g (identityParam (E := E)) hK
    (fun _ _ => _root_.Set.mem_univ _)
  change riemannianVolumeMeasure 𝓘(ℝ, E) E g (id '' K) = _ at hid
  rw [_root_.Set.image_id] at hid
  rw [hid]
  apply _root_.MeasureTheory.setLIntegral_congr_fun hK
  intro w hw
  exact congrArg ENNReal.ofReal (openParam_density g U xU (hKU hw))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_restrictOpen_preimage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_restrictOpen_preimage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_restrictOpen_preimage ``Submission.DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_restrictOpen_preimage

end DifferentialGeometry.Geometry.Measure
