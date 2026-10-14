import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Koszul.Product
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderMetric
import Submission.DifferentialGeometry.Geometry.Connection.ChartFrame.ChartSection
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Chart.Metric
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Inner.InnerBridge

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter
open _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Tensor.Tensor0SRiemannian
open scoped _root_.Manifold _root_.ContDiff _root_.Topology _root_.BigOperators

private abbrev SphereModel := EuclideanSpace ℝ (Fin 2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereModel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereModel target :: scope.openDecls } }
private abbrev CylinderModel := SphereModel × ℝ

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderModel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderModel target :: scope.openDecls } }

private local instance cylinderSphereOneNormedGroup : NormedAddCommGroup (SphereModel →L[ℝ] ℝ) := inferInstance

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderSphereOneNormedGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderSphereOneNormedGroup target :: scope.openDecls } }
private local instance cylinderSphereOneNormedSpace : NormedSpace ℝ (SphereModel →L[ℝ] ℝ) := inferInstance

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderSphereOneNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderSphereOneNormedSpace target :: scope.openDecls } }
private local instance cylinderSphereTwoNormedGroup : NormedAddCommGroup (SphereModel →L[ℝ] SphereModel →L[ℝ] ℝ) := inferInstance

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderSphereTwoNormedGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderSphereTwoNormedGroup target :: scope.openDecls } }
private local instance cylinderSphereTwoNormedSpace : NormedSpace ℝ (SphereModel →L[ℝ] SphereModel →L[ℝ] ℝ) := inferInstance

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderSphereTwoNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderSphereTwoNormedSpace target :: scope.openDecls } }
private local instance cylinderOneNormedGroup : NormedAddCommGroup (CylinderModel →L[ℝ] ℝ) := inferInstance

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderOneNormedGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderOneNormedGroup target :: scope.openDecls } }
private local instance cylinderOneNormedSpace : NormedSpace ℝ (CylinderModel →L[ℝ] ℝ) := inferInstance

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderOneNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderOneNormedSpace target :: scope.openDecls } }
private local instance cylinderTwoNormedGroup : NormedAddCommGroup (CylinderModel →L[ℝ] CylinderModel →L[ℝ] ℝ) := inferInstance

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderTwoNormedGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderTwoNormedGroup target :: scope.openDecls } }
private local instance cylinderTwoNormedSpace : NormedSpace ℝ (CylinderModel →L[ℝ] CylinderModel →L[ℝ] ℝ) := inferInstance

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderTwoNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderTwoNormedSpace target :: scope.openDecls } }

private local instance cylinderChartSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderChartSphereDimension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderChartSphereDimension target :: scope.openDecls } }

private theorem cylinder_chart_source (p x : SpatialNeckCylinder)
    (hx : x.1 ∈ (chartAt SphereModel p.1).source) :
    x ∈ (chartAt (ModelProd SphereModel ℝ) p).source := by
  exact ⟨hx, _root_.Set.mem_univ x.2⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinder_chart_source
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinder_chart_source target :: scope.openDecls } }

private theorem cylinder_mfderiv_prodMap_space (x : SpatialNeckCylinder)
    (f : SpatialNeckSphere → SphereModel)
    (hf : MDifferentiableAt (𝓡 2) 𝓘(ℝ, SphereModel) f x.1) :
    mfderiv SpatialNeckCylinderModel 𝓘(ℝ, CylinderModel) (Prod.map f id) x =
      (mfderiv (𝓡 2) 𝓘(ℝ, SphereModel) f x.1).prodMap
        (ContinuousLinearMap.id ℝ ℝ) := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  rw [mfderiv_prodMap hf mdifferentiableAt_id, mfderiv_id]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinder_mfderiv_prodMap_space
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinder_mfderiv_prodMap_space target :: scope.openDecls } }


theorem cylinder_trivToE (p x : SpatialNeckCylinder)
    (hx : x.1 ∈ (chartAt SphereModel p.1).source)
    (v : TangentSpace SpatialNeckCylinderModel x) :
    trivToE (I := SpatialNeckCylinderModel) p x v =
      (trivToE (I := 𝓡 2) p.1 x.1 v.1, v.2) := by
  have hprod := cylinder_chart_source p x hx
  have hfun : (extChartAt SpatialNeckCylinderModel p : SpatialNeckCylinder → CylinderModel) =
      Prod.map (extChartAt (𝓡 2) p.1) id := by
    rw [extChartAt_prod]
    rfl
  rw [trivToE, TangentBundle.continuousLinearMapAt_trivializationAt hprod, hfun]
  rw [cylinder_mfderiv_prodMap_space x _ (mdifferentiableAt_extChartAt hx)]
  rw [trivToE, TangentBundle.continuousLinearMapAt_trivializationAt hx]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinder_trivToE then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinder_trivToE"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinder_trivToE ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinder_trivToE


theorem cylinder_trivFromE (p x : SpatialNeckCylinder)
    (hx : x.1 ∈ (chartAt SphereModel p.1).source) (v : CylinderModel) :
    trivFromE (I := SpatialNeckCylinderModel) p x v =
      (trivFromE (I := 𝓡 2) p.1 x.1 v.1, v.2) := by
  have hprod : x ∈ (_root_.FiberBundle.trivializationAt CylinderModel
      (TangentSpace SpatialNeckCylinderModel) p).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact cylinder_chart_source p x hx
  have hsphere : x.1 ∈ (_root_.FiberBundle.trivializationAt SphereModel (TangentSpace (𝓡 2)) p.1).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hx
  let w := trivFromE (I := SpatialNeckCylinderModel) p x v
  have hpair : (trivToE (I := 𝓡 2) p.1 x.1 w.1, w.2) = v :=
    (cylinder_trivToE p x hx w).symm.trans
      (trivToE_trivFromE (I := SpatialNeckCylinderModel) p hprod v)
  have hsecond := congrArg (fun z : CylinderModel => z.2) hpair
  change (w : CylinderModel) = (trivFromE (I := 𝓡 2) p.1 x.1 v.1, v.2)
  apply Prod.ext
  · have hh := congrArg (trivFromE (I := 𝓡 2) p.1 x.1) (congrArg Prod.fst hpair)
    exact (trivFromE_trivToE (I := 𝓡 2) p.1 hsphere w.1).symm.trans hh
  · exact hsecond

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinder_trivFromE then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinder_trivFromE"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinder_trivFromE ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinder_trivFromE


theorem shrinkingCylinder_chartGramBilin (s : ℝ) (hs : s < 1)
    (p x : SpatialNeckCylinder) (hx : x.1 ∈ (chartAt SphereModel p.1).source) :
    chartGramBilin (scalarOneShrinkingCylinderMetric s hs) p x =
      lineProductMetricForm
        (chartGramBilin (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) p.1 x.1)
        (2 * (1 - s)) := by
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  calc
    _ = (scalarOneShrinkingCylinderMetric s hs).inner x
        (trivFromE (I := SpatialNeckCylinderModel) p x v)
        (trivFromE (I := SpatialNeckCylinderModel) p x w) := by
      simp only [chartGramBilin_eq_innerJinv, modelInnerAt_apply, chartJinv_apply,
        ContinuousLinearEquiv.symm_apply_apply]
    _ = 2 * (1 - s) *
        (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner x.1
          (trivFromE (I := 𝓡 2) p.1 x.1 v.1) (trivFromE (I := 𝓡 2) p.1 x.1 w.1) +
        v.2 * w.2 := by
      rw [cylinder_trivFromE p x hx v, cylinder_trivFromE p x hx w]
      exact scalarOneShrinkingCylinderMetric_inner s hs x.1 x.2 _ _ v.2 w.2
    _ = _ := by
      simp only [lineProductMetricForm_apply, chartGramBilin_eq_innerJinv,
        modelInnerAt_apply, chartJinv_apply, ContinuousLinearEquiv.symm_apply_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.shrinkingCylinder_chartGramBilin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.shrinkingCylinder_chartGramBilin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.shrinkingCylinder_chartGramBilin ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.shrinkingCylinder_chartGramBilin


theorem shrinkingCylinder_chartGramBilin_in_coordinates (s : ℝ) (hs : s < 1)
    (p : SpatialNeckCylinder) (y : CylinderModel)
    (hy : y ∈ (extChartAt SpatialNeckCylinderModel p).target) :
    chartGramBilin (scalarOneShrinkingCylinderMetric s hs) p
        ((extChartAt SpatialNeckCylinderModel p).symm y) =
      lineProductMetricForm
        (chartGramBilin (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))
          p.1 ((extChartAt (𝓡 2) p.1).symm y.1)) (2 * (1 - s)) := by
  have hsource := (extChartAt SpatialNeckCylinderModel p).map_target hy
  rw [extChartAt_source] at hsource
  have hx : ((extChartAt SpatialNeckCylinderModel p).symm y).1 ∈
      (chartAt SphereModel p.1).source := hsource.1
  have hform := shrinkingCylinder_chartGramBilin s hs p _ hx
  have hfst : ((extChartAt SpatialNeckCylinderModel p).symm y).1 =
      (extChartAt (𝓡 2) p.1).symm y.1 := by
    rw [extChartAt_prod]
    rfl
  rw [hfst] at hform
  exact hform

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.shrinkingCylinder_chartGramBilin_in_coordinates then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.shrinkingCylinder_chartGramBilin_in_coordinates"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.shrinkingCylinder_chartGramBilin_in_coordinates ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.shrinkingCylinder_chartGramBilin_in_coordinates

private theorem chartGramBilin_coordinates_differentiableAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M) (p : M) {y : E}
    (hy : y ∈ interior (extChartAt I p).target) :
    DifferentiableAt ℝ (fun u => chartGramBilin g p ((extChartAt I p).symm u)) y := by
  classical
  let : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  change DifferentiableAt ℝ (fun u =>
    ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      chartGramOnE g p i j u • (chartCoordCLM E i).smulRight (chartCoordCLM E j)) y
  refine DifferentiableAt.fun_sum (fun i _ => ?_)
  refine DifferentiableAt.fun_sum (fun j _ => ?_)
  exact (chartGramOnE_differentiableAt_int g p i j hy).smul_const _

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.chartGramBilin_coordinates_differentiableAt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.chartGramBilin_coordinates_differentiableAt target :: scope.openDecls } }


theorem shrinkingCylinder_chartGramBilin_hasFDerivAt (s : ℝ) (hs : s < 1)
    (p : SpatialNeckCylinder) (y : CylinderModel)
    (hy : y ∈ (extChartAt SpatialNeckCylinderModel p).target) :
    HasFDerivAt (fun u => chartGramBilin (scalarOneShrinkingCylinderMetric s hs) p
        ((extChartAt SpatialNeckCylinderModel p).symm u))
      (lineProductMetricDerivative
        (fderiv ℝ (fun u => chartGramBilin
          (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) p.1
          ((extChartAt (𝓡 2) p.1).symm u)) y.1) (2 * (1 - s))) y := by
  have hyprod := hy
  rw [extChartAt_prod] at hyprod
  have hysphere : y.1 ∈ interior (extChartAt (𝓡 2) p.1).target := by
    rw [(isOpen_extChartAt_target (I := 𝓡 2) p.1).interior_eq]
    exact hyprod.1
  have hB := chartGramBilin_coordinates_differentiableAt
    (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) p.1 hysphere
  apply (hasFDerivAt_lineProductMetricForm (x := y) hB.hasFDerivAt (2 * (1 - s))).congr_of_eventuallyEq
  filter_upwards [(isOpen_extChartAt_target (I := SpatialNeckCylinderModel) p).mem_nhds hy]
    with u hu
  exact shrinkingCylinder_chartGramBilin_in_coordinates s hs p u hu

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.shrinkingCylinder_chartGramBilin_hasFDerivAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.shrinkingCylinder_chartGramBilin_hasFDerivAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.shrinkingCylinder_chartGramBilin_hasFDerivAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.shrinkingCylinder_chartGramBilin_hasFDerivAt


theorem shrinkingCylinder_chartGramBilin_fderiv (s : ℝ) (hs : s < 1)
    (p : SpatialNeckCylinder) (y : CylinderModel)
    (hy : y ∈ (extChartAt SpatialNeckCylinderModel p).target) :
    fderiv ℝ (fun u => chartGramBilin (scalarOneShrinkingCylinderMetric s hs) p
        ((extChartAt SpatialNeckCylinderModel p).symm u)) y =
      lineProductMetricDerivative
        (fderiv ℝ (fun u => chartGramBilin
          (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) p.1
          ((extChartAt (𝓡 2) p.1).symm u)) y.1) (2 * (1 - s)) :=
  (shrinkingCylinder_chartGramBilin_hasFDerivAt s hs p y hy).fderiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.shrinkingCylinder_chartGramBilin_fderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.shrinkingCylinder_chartGramBilin_fderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.shrinkingCylinder_chartGramBilin_fderiv ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.shrinkingCylinder_chartGramBilin_fderiv

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
