import Submission.DifferentialGeometry.Geometry.Boundary.Manifold.Basic
import Submission.DifferentialGeometry.Bundle.TangentSpace
import Submission.DifferentialGeometry.Bundle.Hom
import Submission.DifferentialGeometry.Analysis.FiniteDimensional.Coercivity
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Chart.Density
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.Bounded

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Set _root_.Function _root_.Topology _root_.Bundle _root_.Manifold _root_.MeasureTheory _root_.Bornology
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

private local instance _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.instNormedAddCommGroupContinuousLinearMapRealId_differentialGeometry : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.instNormedAddCommGroupContinuousLinearMapRealId_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.instNormedAddCommGroupContinuousLinearMapRealId_differentialGeometry target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.instNormedSpaceRealContinuousLinearMapId_differentialGeometry : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.instNormedSpaceRealContinuousLinearMapId_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.instNormedSpaceRealContinuousLinearMapId_differentialGeometry target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.instNormedAddCommGroupContinuousLinearMapRealId_differentialGeometry_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.instNormedAddCommGroupContinuousLinearMapRealId_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.instNormedAddCommGroupContinuousLinearMapRealId_differentialGeometry_1 target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.instNormedSpaceRealContinuousLinearMapId_differentialGeometry_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.instNormedSpaceRealContinuousLinearMapId_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.instNormedSpaceRealContinuousLinearMapId_differentialGeometry_1 target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.instContinuousAddContinuousLinearMapRealIdTangentSpace_differentialGeometry (x : M) : ContinuousAdd (TangentSpace I x →L[ℝ] ℝ) :=
  (ContinuousLinearMap.topologicalAddGroup (𝕜₁ := ℝ) (𝕜₂ := ℝ)).toContinuousAdd

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.instContinuousAddContinuousLinearMapRealIdTangentSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.instContinuousAddContinuousLinearMapRealIdTangentSpace_differentialGeometry target :: scope.openDecls } }

private def Phi (I : ModelWithCorners ℝ E H) [hI : HasSmoothBoundary E H I] :
    hI.boundaryE → E :=
  (I : H → E) ∘ hI.inclH ∘ hI.boundaryI.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.Phi
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.Phi target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private lemma Phi_eq (I : ModelWithCorners ℝ E H) [hI : HasSmoothBoundary E H I] :
    Phi I = (I : H → E) ∘ hI.inclH ∘ hI.boundaryI.symm := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.Phi_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.Phi_eq target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private lemma Phi_contDiff (I : ModelWithCorners ℝ E H)
    [hI : HasSmoothBoundary E H I] :
    ContDiff ℝ ∞ (Phi I) :=
  hI.I_inclH_boundaryI_symm_contDiff

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.Phi_contDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.Phi_contDiff target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private lemma projE_comp_Phi (I : ModelWithCorners ℝ E H)
    [hI : HasSmoothBoundary E H I] :
    hI.projE ∘ Phi I = id := by
  funext e
  have h1 : hI.projE (I (hI.inclH (hI.boundaryI.symm e)))
      = hI.boundaryI (hI.boundaryI.symm e) :=
    hI.proj_inclH_compat (hI.boundaryI.symm e)
  have h2 : hI.boundaryI (hI.boundaryI.symm e) = e := by
    have hmem : e ∈ Set.range hI.boundaryI := by
      rw [hI.boundaryI.range_eq_univ]; exact Set.mem_univ _
    rcases hmem with ⟨b, rfl⟩
    rw [hI.boundaryI.left_inv b]
  change hI.projE (Phi I e) = e
  rw [Phi_eq]
  simpa [Function.comp] using h1.trans h2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.projE_comp_Phi
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.projE_comp_Phi target :: scope.openDecls } }

private lemma infty_ne_zero_withTopENat : (∞ : WithTop ℕ∞) ≠ 0 := by
  intro h
  have h' : ((⊤ : ℕ∞) : WithTop ℕ∞) = ((0 : ℕ∞) : WithTop ℕ∞) := h
  exact ENat.top_ne_zero (WithTop.coe_eq_coe.mp h')

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.infty_ne_zero_withTopENat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.infty_ne_zero_withTopENat target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
theorem boundaryInclusion_contMDiff
    [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M] :
    ContMDiff hI.boundaryI I ∞ (boundaryInclusion I M) := by
  refine contMDiff_of_locally_contMDiffOn ?_
  intro x
  by_cases hN : Nonempty hI.boundaryH
  · have := hN
    refine ⟨BoundaryManifold.boundaryChartSource (I := I) x,
      BoundaryManifold.isOpen_boundaryChartSource (I := I) x,
      BoundaryManifold.mem_boundaryChartSource_self (I := I) x, ?_⟩
    have h_chart_eq : chartAt hI.boundaryH x = BoundaryManifold.boundaryChart (I := I) x := by
      change BoundaryManifold.defaultBoundaryChart (I := I) x =
        BoundaryManifold.boundaryChart (I := I) x
      exact BoundaryManifold.defaultBoundaryChart_eq_boundaryChart (I := I) x
    have hs : BoundaryManifold.boundaryChartSource (I := I) x ⊆
        (chartAt hI.boundaryH x).source := by
      intro y hy
      rw [h_chart_eq]
      change y ∈ BoundaryManifold.boundaryChartSource (I := I) x
      exact hy
    have h2s : _root_.Set.MapsTo (boundaryInclusion I M)
        (BoundaryManifold.boundaryChartSource (I := I) x)
        (chartAt H ((boundaryInclusion I M x : M))).source := by
      intro y hy
      change (y : M) ∈ (chartAt H (x : M)).source at hy
      change (y : M) ∈ (chartAt H ((x : M))).source
      exact hy
    rw [contMDiffOn_iff_of_subset_source (x := x) (y := (x : M)) hs h2s]
    refine ⟨continuous_subtype_val.continuousOn, ?_⟩
    have hPhi : ContDiff ℝ ∞ (Phi I) := Phi_contDiff I
    refine hPhi.contDiffOn.congr ?_
    intro e he
    rcases he with ⟨y, hy_source, hy_eq⟩
    change (y : M) ∈ (chartAt H (x : M)).source at hy_source
    change (extChartAt I (boundaryInclusion I M x) ∘ boundaryInclusion I M ∘
      (extChartAt hI.boundaryI x).symm) e = Phi I e
    simp only [Function.comp_apply]
    have h_e_eq :
        e = hI.boundaryI (BoundaryManifold.boundaryChart (I := I) x y) := by
      rw [← hy_eq]
      change hI.boundaryI (chartAt hI.boundaryH x y) =
        hI.boundaryI (BoundaryManifold.boundaryChart (I := I) x y)
      rw [h_chart_eq]
    have h_y_in_source :
        y ∈ (BoundaryManifold.boundaryChart (I := I) x).source := hy_source
    have h_inv : (extChartAt hI.boundaryI x).symm e = y := by
      rw [h_e_eq]
      change (chartAt hI.boundaryH x).symm
          (hI.boundaryI.symm (hI.boundaryI
            (BoundaryManifold.boundaryChart (I := I) x y))) = y
      rw [hI.boundaryI.left_inv]
      rw [h_chart_eq]
      exact (BoundaryManifold.boundaryChart (I := I) x).left_inv h_y_in_source
    rw [h_inv]
    have hinclH := BoundaryManifold.inclH_boundaryChart_apply
      (I := I) x y hy_source
    change I (chartAt H (x : M) (y : M)) = Phi I e
    rw [h_e_eq, Phi_eq]
    simp only [Function.comp_apply]
    rw [hI.boundaryI.left_inv]
    rw [hinclH]
  · have : IsEmpty hI.boundaryH := not_nonempty_iff.mp hN
    have : IsEmpty (BoundaryManifold I M) :=
      BoundaryManifold.isEmpty_of_isEmpty_boundaryH (I := I)
    exact (IsEmpty.false x).elim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryInclusion_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryInclusion_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryInclusion_contMDiff ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryInclusion_contMDiff

variable [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]

private local instance _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.instNormedAddCommGroupContinuousLinearMapRealIdBoundaryE : NormedAddCommGroup (hI.boundaryE →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.instNormedAddCommGroupContinuousLinearMapRealIdBoundaryE
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.instNormedAddCommGroupContinuousLinearMapRealIdBoundaryE target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.instNormedSpaceRealContinuousLinearMapIdBoundaryE : NormedSpace ℝ (hI.boundaryE →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.instNormedSpaceRealContinuousLinearMapIdBoundaryE
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.instNormedSpaceRealContinuousLinearMapIdBoundaryE target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.instNormedAddCommGroupContinuousLinearMapRealIdBoundaryE_1 : NormedAddCommGroup (hI.boundaryE →L[ℝ] hI.boundaryE →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.instNormedAddCommGroupContinuousLinearMapRealIdBoundaryE_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.instNormedAddCommGroupContinuousLinearMapRealIdBoundaryE_1 target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.instNormedSpaceRealContinuousLinearMapIdBoundaryE_1 : NormedSpace ℝ (hI.boundaryE →L[ℝ] hI.boundaryE →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.instNormedSpaceRealContinuousLinearMapIdBoundaryE_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.instNormedSpaceRealContinuousLinearMapIdBoundaryE_1 target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.instContinuousAddContinuousLinearMapRealIdTangentSpaceBoundaryEBoundaryHBoundaryIBoundaryManifold (x : BoundaryManifold I M) :
    ContinuousAdd (TangentSpace hI.boundaryI x →L[ℝ] ℝ) :=
  (ContinuousLinearMap.topologicalAddGroup (𝕜₁ := ℝ) (𝕜₂ := ℝ)).toContinuousAdd

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.instContinuousAddContinuousLinearMapRealIdTangentSpaceBoundaryEBoundaryHBoundaryIBoundaryManifold
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.instContinuousAddContinuousLinearMapRealIdTangentSpaceBoundaryEBoundaryHBoundaryIBoundaryManifold target :: scope.openDecls } }


noncomputable def boundaryInclusionMfderiv (x : BoundaryManifold I M) :
    TangentSpace hI.boundaryI x →L[ℝ] TangentSpace I (x : M) :=
  mfderiv hI.boundaryI I (boundaryInclusion I M) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryInclusionMfderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryInclusionMfderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryInclusionMfderiv ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryInclusionMfderiv

private noncomputable def boundaryInclusionModelMfderiv
    (x : BoundaryManifold I M) : hI.boundaryE →L[ℝ] E :=
  (tangentSpaceModelContinuousLinearEquiv (I := hI.boundaryI) x).arrowCongr
    (tangentSpaceModelContinuousLinearEquiv (I := I) (x : M))
    (boundaryInclusionMfderiv x)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryInclusionModelMfderiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryInclusionModelMfderiv target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
@[simp] private lemma boundaryInclusionModelMfderiv_apply
    (x : BoundaryManifold I M) (v : hI.boundaryE) :
    boundaryInclusionModelMfderiv x v =
      tangentSpaceModelContinuousLinearEquiv (I := I) (x : M)
        (boundaryInclusionMfderiv x
          ((tangentSpaceModelContinuousLinearEquiv (I := hI.boundaryI) x).symm v)) := by
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryInclusionModelMfderiv_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryInclusionModelMfderiv_apply target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
@[simp] lemma dincl_eq (x : BoundaryManifold I M) :
    (boundaryInclusionMfderiv x :
      TangentSpace hI.boundaryI x →L[ℝ] TangentSpace I (x : M)) =
      mfderiv hI.boundaryI I (boundaryInclusion I M) x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.dincl_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.dincl_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.dincl_eq ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.dincl_eq

omit [FiniteDimensional ℝ E] in
private lemma boundaryInclusion_mdifferentiableAt (x : BoundaryManifold I M) :
    MDifferentiableAt hI.boundaryI I (boundaryInclusion I M) x :=
  (boundaryInclusion_contMDiff (I := I) (M := M)).mdifferentiableAt
    infty_ne_zero_withTopENat

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryInclusion_mdifferentiableAt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryInclusion_mdifferentiableAt target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
theorem boundaryInclusionMfderiv_model_eq_fderiv (x : BoundaryManifold I M) :
    (tangentSpaceModelContinuousLinearEquiv (I := hI.boundaryI) x).arrowCongr
        (tangentSpaceModelContinuousLinearEquiv (I := I) (x : M))
        (boundaryInclusionMfderiv x) =
      fderiv ℝ ((I : H → E) ∘ hI.inclH ∘ hI.boundaryI.symm)
        (extChartAt hI.boundaryI x x) := by
  have : Nonempty hI.boundaryH := ⟨chartAt hI.boundaryH x x⟩
  change boundaryInclusionModelMfderiv x = fderiv ℝ (Phi I) (extChartAt hI.boundaryI x x)
  unfold boundaryInclusionModelMfderiv boundaryInclusionMfderiv
  unfold tangentSpaceModelContinuousLinearEquiv
  rw [(boundaryInclusion_mdifferentiableAt (I := I) (M := M) x).mfderiv]
  have h_range : Set.range hI.boundaryI = Set.univ := hI.boundaryI.range_eq_univ
  rw [h_range, fderivWithin_univ]
  have h_chart_eq : chartAt hI.boundaryH x = BoundaryManifold.boundaryChart (I := I) x := by
    change BoundaryManifold.defaultBoundaryChart (I := I) x =
      BoundaryManifold.boundaryChart (I := I) x
    exact BoundaryManifold.defaultBoundaryChart_eq_boundaryChart (I := I) x
  have h_eq : (writtenInExtChartAt hI.boundaryI I x (boundaryInclusion I M))
      =ᶠ[𝓝 (extChartAt hI.boundaryI x x)] Phi I := by
    have h_target_mem : (extChartAt hI.boundaryI x).target ∈
        𝓝 (extChartAt hI.boundaryI x x) :=
      extChartAt_target_mem_nhds (I := hI.boundaryI) (M := BoundaryManifold I M) x
    filter_upwards [h_target_mem] with e he
    have he_target_chart : hI.boundaryI.symm e ∈ (chartAt hI.boundaryH x).target := by
      rw [extChartAt_target] at he
      exact he.1
    rw [h_chart_eq] at he_target_chart
    have h_extChart_symm_val :
        (((extChartAt hI.boundaryI x).symm e : BoundaryManifold I M) : M) =
          (chartAt H (x : M)).symm (hI.inclH (hI.boundaryI.symm e)) := by
      change (((chartAt hI.boundaryH x).symm (hI.boundaryI.symm e) :
          BoundaryManifold I M) : M) = _
      rw [h_chart_eq]
      exact BoundaryManifold.boundaryChartInvFun_val_of_mem_target
        (I := I) x he_target_chart
    change writtenInExtChartAt hI.boundaryI I x (boundaryInclusion I M) e = Phi I e
    unfold writtenInExtChartAt
    simp only [Function.comp_apply]
    change extChartAt I (boundaryInclusion I M x)
        (((extChartAt hI.boundaryI x).symm e : BoundaryManifold I M) : M) = Phi I e
    rw [h_extChart_symm_val]
    change I (chartAt H (x : M) ((chartAt H (x : M)).symm
      (hI.inclH (hI.boundaryI.symm e)))) = Phi I e
    rw [(chartAt H (x : M)).right_inv he_target_chart]
    rfl
  rw [Filter.EventuallyEq.fderiv_eq h_eq]
  ext v
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryInclusionMfderiv_model_eq_fderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryInclusionMfderiv_model_eq_fderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryInclusionMfderiv_model_eq_fderiv ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryInclusionMfderiv_model_eq_fderiv

omit [FiniteDimensional ℝ E] in
private lemma fderiv_Phi_injective (e : hI.boundaryE) :
    Function.Injective (fderiv ℝ (Phi I) e) := by
  have h_proj_phi : hI.projE ∘ Phi I = id := projE_comp_Phi I
  have hPhi : ContDiff ℝ ∞ (Phi I) := Phi_contDiff I
  have hproj : ContDiff ℝ ∞ hI.projE := hI.projE_contDiff
  have hPhi_diff : Differentiable ℝ (Phi I) := hPhi.differentiable (by simp)
  have hproj_diff : Differentiable ℝ hI.projE := hproj.differentiable (by simp)
  have h_chain : fderiv ℝ (hI.projE ∘ Phi I) e =
      (fderiv ℝ hI.projE (Phi I e)).comp (fderiv ℝ (Phi I) e) :=
    fderiv_comp e (hproj_diff (Phi I e)) (hPhi_diff e)
  have h_id_eq : fderiv ℝ (hI.projE ∘ Phi I) e =
      ContinuousLinearMap.id ℝ hI.boundaryE := by
    rw [h_proj_phi]; exact fderiv_id
  have h_comp_id : (fderiv ℝ hI.projE (Phi I e)).comp (fderiv ℝ (Phi I) e) =
      ContinuousLinearMap.id ℝ hI.boundaryE := by
    rw [← h_chain, h_id_eq]
  intro v w hvw
  have h_apply :
      (fderiv ℝ hI.projE (Phi I e)).comp (fderiv ℝ (Phi I) e) v =
      (fderiv ℝ hI.projE (Phi I e)).comp (fderiv ℝ (Phi I) e) w := by
    simp [hvw]
  rw [h_comp_id] at h_apply
  simpa using h_apply

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.fderiv_Phi_injective
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.fderiv_Phi_injective target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
lemma dincl_injective (x : BoundaryManifold I M) :
    Function.Injective (boundaryInclusionMfderiv x) := by
  by_cases hN : Nonempty hI.boundaryH
  · have := hN
    have h_model : Function.Injective (boundaryInclusionModelMfderiv x) := by
      change Function.Injective
        ((tangentSpaceModelContinuousLinearEquiv (I := hI.boundaryI) x).arrowCongr
          (tangentSpaceModelContinuousLinearEquiv (I := I) (x : M))
          (boundaryInclusionMfderiv x))
      rw [boundaryInclusionMfderiv_model_eq_fderiv]
      exact fderiv_Phi_injective (extChartAt hI.boundaryI x x)
    intro v w hvw
    apply (tangentSpaceModelContinuousLinearEquiv (I := hI.boundaryI) x).injective
    apply h_model
    change tangentSpaceModelContinuousLinearEquiv (I := I) (x : M)
        (boundaryInclusionMfderiv x v) =
      tangentSpaceModelContinuousLinearEquiv (I := I) (x : M)
        (boundaryInclusionMfderiv x w)
    exact congrArg (tangentSpaceModelContinuousLinearEquiv (I := I) (x : M)) hvw
  · have : IsEmpty hI.boundaryH := not_nonempty_iff.mp hN
    have : IsEmpty (BoundaryManifold I M) :=
      BoundaryManifold.isEmpty_of_isEmpty_boundaryH (I := I)
    exact (IsEmpty.false x).elim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.dincl_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.dincl_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.dincl_injective ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.dincl_injective

private noncomputable def ambientMetricInnerModel
    (g : SmoothRiemannianMetric I M) (x : M) : E →L[ℝ] E →L[ℝ] ℝ :=
  let e := tangentSpaceModelContinuousLinearEquiv (I := I) x
  e.arrowCongr (e.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)) (g.inner x)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.ambientMetricInnerModel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.ambientMetricInnerModel target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] hI in
@[simp] private lemma ambientMetricInnerModel_apply
    (g : SmoothRiemannianMetric I M) (x : M) (v w : E) :
    ambientMetricInnerModel g x v w =
      g.inner x
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm v)
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm w) := by
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.ambientMetricInnerModel_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.ambientMetricInnerModel_apply target :: scope.openDecls } }

private noncomputable def inducedMetricInnerModel
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M) :
    hI.boundaryE →L[ℝ] hI.boundaryE →L[ℝ] ℝ :=
  (ambientMetricInnerModel g (x : M)).bilinearComp
    (boundaryInclusionModelMfderiv x) (boundaryInclusionModelMfderiv x)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetricInnerModel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetricInnerModel target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
@[simp] private lemma inducedMetricInnerModel_apply_ambient
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M)
    (v w : hI.boundaryE) :
    inducedMetricInnerModel g x v w =
      g.inner (x : M)
        (boundaryInclusionMfderiv x
          ((tangentSpaceModelContinuousLinearEquiv (I := hI.boundaryI) x).symm v))
        (boundaryInclusionMfderiv x
          ((tangentSpaceModelContinuousLinearEquiv (I := hI.boundaryI) x).symm w)) := by
  rw [inducedMetricInnerModel, ContinuousLinearMap.bilinearComp_apply,
    ambientMetricInnerModel_apply, boundaryInclusionModelMfderiv_apply,
    boundaryInclusionModelMfderiv_apply]
  rw [(tangentSpaceModelContinuousLinearEquiv (I := I) (x : M)).symm_apply_apply,
    (tangentSpaceModelContinuousLinearEquiv (I := I) (x : M)).symm_apply_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetricInnerModel_apply_ambient
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetricInnerModel_apply_ambient target :: scope.openDecls } }

noncomputable def inducedMetricInner
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M) :
    TangentSpace hI.boundaryI x →L[ℝ] TangentSpace hI.boundaryI x →L[ℝ] ℝ :=
  let e := tangentSpaceModelContinuousLinearEquiv (I := hI.boundaryI) x
  (e.arrowCongr (e.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ))).symm
    (inducedMetricInnerModel g x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetricInner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetricInner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetricInner ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetricInner

omit [FiniteDimensional ℝ E] in
@[simp] lemma inducedMetricInner_apply
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M)
    (v w : TangentSpace hI.boundaryI x) :
    inducedMetricInner g x v w = g.inner (x : M) (boundaryInclusionMfderiv x v)
      (boundaryInclusionMfderiv x w) := by
  simp only [inducedMetricInner, ContinuousLinearEquiv.arrowCongr_symm,
    ContinuousLinearEquiv.arrowCongr_apply]
  simp only [ContinuousLinearEquiv.symm_symm, ContinuousLinearEquiv.refl_symm,
    ContinuousLinearEquiv.refl_apply]
  rw [inducedMetricInnerModel_apply_ambient]
  rw [(tangentSpaceModelContinuousLinearEquiv (I := hI.boundaryI) x).symm_apply_apply,
    (tangentSpaceModelContinuousLinearEquiv (I := hI.boundaryI) x).symm_apply_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetricInner_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetricInner_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetricInner_apply ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetricInner_apply

omit [FiniteDimensional ℝ E] in
private lemma inducedMetricInnerModel_apply
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M)
    (v w : hI.boundaryE) :
    inducedMetricInnerModel g x v w =
      inducedMetricInner g x
        ((tangentSpaceModelContinuousLinearEquiv (I := hI.boundaryI) x).symm v)
        ((tangentSpaceModelContinuousLinearEquiv (I := hI.boundaryI) x).symm w) := by
  rw [inducedMetricInner_apply]
  rw [inducedMetricInnerModel_apply_ambient]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetricInnerModel_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetricInnerModel_apply target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
lemma inducedMetricInner_symm
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M)
    (v w : TangentSpace hI.boundaryI x) :
    inducedMetricInner g x v w = inducedMetricInner g x w v := by
  rw [inducedMetricInner_apply, inducedMetricInner_apply]
  exact g.symm (x : M) (boundaryInclusionMfderiv x v) (boundaryInclusionMfderiv x w)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetricInner_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetricInner_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetricInner_symm ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetricInner_symm

omit [FiniteDimensional ℝ E] in
lemma inducedMetricInner_pos
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M)
    (v : TangentSpace hI.boundaryI x) (hv : v ≠ 0) :
    0 < inducedMetricInner g x v v := by
  rw [inducedMetricInner_apply]
  apply g.pos (x : M) (boundaryInclusionMfderiv x v)
  intro h0
  apply hv
  have h_zero : (boundaryInclusionMfderiv x) (0 : TangentSpace hI.boundaryI x) = 0 := map_zero _
  exact dincl_injective (I := I) (M := M) x (h0.trans h_zero.symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetricInner_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetricInner_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetricInner_pos ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetricInner_pos

omit [FiniteDimensional ℝ E] in
lemma inducedMetricInner_isVonNBounded
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M) :
    _root_.Bornology.IsVonNBounded ℝ
      {v : TangentSpace hI.boundaryI x | inducedMetricInner g x v v < 1} := by
  have hc := (inducedMetricInnerModel g x).isCoercive_of_posDef
    (fun v hv => by
      rw [inducedMetricInnerModel_apply]
      apply inducedMetricInner_pos (I := I) (M := M) g x
      exact (tangentSpaceModelContinuousLinearEquiv (I := hI.boundaryI) x).symm.injective.ne hv)
  have h_model : _root_.Bornology.IsVonNBounded ℝ
      {v : hI.boundaryE | inducedMetricInnerModel g x v v < 1} :=
    NormedSpace.isVonNBounded_of_isBounded ℝ
      ((hc.isBounded_le 1).subset (by
        intro v hv
        exact show inducedMetricInnerModel g x v v ≤ 1 from le_of_lt hv))
  let e := tangentSpaceModelContinuousLinearEquiv (I := hI.boundaryI) x
  have h_image := h_model.image e.symm.toContinuousLinearMap
  have h_set : e.symm.toContinuousLinearMap ''
        {v : hI.boundaryE | inducedMetricInnerModel g x v v < 1} =
      {v : TangentSpace hI.boundaryI x | inducedMetricInner g x v v < 1} := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      change inducedMetricInner g x (e.symm w) (e.symm w) < 1
      rw [← inducedMetricInnerModel_apply]
      exact hw
    · intro hv
      refine ⟨e v, ?_, e.symm_apply_apply v⟩
      change inducedMetricInnerModel g x (e v) (e v) < 1
      rw [inducedMetricInnerModel_apply]
      rw [e.symm_apply_apply]
      exact hv
  rwa [h_set] at h_image

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetricInner_isVonNBounded then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetricInner_isVonNBounded"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetricInner_isVonNBounded ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetricInner_isVonNBounded

private noncomputable def gInnerCharted
    (g : SmoothRiemannianMetric I M) (x₀ : M) (b : M) : E →L[ℝ] E →L[ℝ] ℝ :=
  ((_root_.FiberBundle.trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
      (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x₀)
    ⟨b, g.inner b⟩).2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.gInnerCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.gInnerCharted target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] hI in
private lemma gInnerCharted_contMDiffAt
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (gInnerCharted (I := I) (M := M) g x₀) x₀ := by
  have h_section : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) b (g.inner b)) :=
    g.contMDiff
  have h_x₀ : x₀ ∈ (_root_.FiberBundle.trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
      (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x₀).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x₀
  exact ((_root_.FiberBundle.trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
      (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x₀).contMDiffAt_section_iff h_x₀).mp
    h_section.contMDiffAt

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.gInnerCharted_contMDiffAt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.gInnerCharted_contMDiffAt target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private lemma gInnerCharted_along_inclusion_contMDiffAt
    (g : SmoothRiemannianMetric I M) (x₀ : BoundaryManifold I M) :
    ContMDiffAt hI.boundaryI 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun b : BoundaryManifold I M =>
        gInnerCharted (I := I) (M := M) g (x₀ : M) (b : M)) x₀ := by
  have h_inclusion_at : ContMDiffAt hI.boundaryI I ∞ (boundaryInclusion I M) x₀ :=
    boundaryInclusion_contMDiff.contMDiffAt
  have h_at : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (gInnerCharted (I := I) (M := M) g (x₀ : M)) (x₀ : M) :=
    gInnerCharted_contMDiffAt g (x₀ : M)
  exact h_at.comp x₀ h_inclusion_at

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.gInnerCharted_along_inclusion_contMDiffAt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.gInnerCharted_along_inclusion_contMDiffAt target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] hI in
private lemma gInnerCharted_eval
    (g : SmoothRiemannianMetric I M) (x₀ b : M)
    (hb : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet) (v w : E) :
    gInnerCharted (I := I) (M := M) g x₀ b v w =
      g.inner b
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).symm b v)
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).symm b w) := by
  change ((_root_.FiberBundle.trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
    (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x₀)
      ⟨b, g.inner b⟩).2 v w = _
  rw [hom_trivializationAt_apply]
  rw [inCoordinates_apply_eq₂ (𝕜 := ℝ) hb hb (Set.mem_univ _)]
  change (_root_.FiberBundle.trivializationAt ℝ (Bundle.Trivial M ℝ) x₀).linearMapAt ℝ b _ = _
  change (Bundle.Trivial.trivialization M ℝ).linearMapAt ℝ b _ = _
  rw [Bundle.Trivial.linearMapAt_trivialization (𝕜 := ℝ) (B := M) (F := ℝ) b]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.gInnerCharted_eval
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.gInnerCharted_eval target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private lemma inducedMetricInner_chart_eval
    (g : SmoothRiemannianMetric I M) (x₀ : BoundaryManifold I M)
    (b : BoundaryManifold I M)
    (hb_ambient : (b : M) ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) (x₀ : M)).baseSet)
    (hb_bdy : b ∈ (_root_.FiberBundle.trivializationAt hI.boundaryE
        (TangentSpace hI.boundaryI) x₀).baseSet) (v w : hI.boundaryE) :
    ((_root_.FiberBundle.trivializationAt (hI.boundaryE →L[ℝ] hI.boundaryE →L[ℝ] ℝ)
        (fun y : BoundaryManifold I M =>
          TangentSpace hI.boundaryI y →L[ℝ]
          TangentSpace hI.boundaryI y →L[ℝ] ℝ) x₀)
      ⟨b, inducedMetricInner g b⟩).2 v w =
    gInnerCharted (I := I) (M := M) g (x₀ : M) (b : M)
      ((_root_.FiberBundle.trivializationAt E (TangentSpace I) (x₀ : M)).continuousLinearMapAt ℝ (b : M)
        (boundaryInclusionMfderiv b ((_root_.FiberBundle.trivializationAt hI.boundaryE
          (TangentSpace hI.boundaryI) x₀).symm b v)))
      ((_root_.FiberBundle.trivializationAt E (TangentSpace I) (x₀ : M)).continuousLinearMapAt ℝ (b : M)
        (boundaryInclusionMfderiv b ((_root_.FiberBundle.trivializationAt hI.boundaryE
          (TangentSpace hI.boundaryI) x₀).symm b w))) := by
  rw [hom_trivializationAt_apply]
  rw [inCoordinates_apply_eq₂ (𝕜 := ℝ) hb_bdy hb_bdy (Set.mem_univ _)]
  change (_root_.FiberBundle.trivializationAt ℝ (Bundle.Trivial (BoundaryManifold I M) ℝ) x₀).linearMapAt ℝ b _ = _
  change (Bundle.Trivial.trivialization (BoundaryManifold I M) ℝ).linearMapAt ℝ b _ = _
  rw [Bundle.Trivial.linearMapAt_trivialization (𝕜 := ℝ) (B := BoundaryManifold I M) (F := ℝ) b]
  change inducedMetricInner g b _ _ = _
  rw [inducedMetricInner_apply]
  rw [gInnerCharted_eval g (x₀ : M) (b : M) hb_ambient]
  have hM_v : (_root_.FiberBundle.trivializationAt E (TangentSpace I) (x₀ : M)).symm (b : M)
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) (x₀ : M)).continuousLinearMapAt ℝ (b : M)
          (boundaryInclusionMfderiv b ((_root_.FiberBundle.trivializationAt hI.boundaryE
            (TangentSpace hI.boundaryI) x₀).symm b v)))
      = boundaryInclusionMfderiv b ((_root_.FiberBundle.trivializationAt hI.boundaryE
            (TangentSpace hI.boundaryI) x₀).symm b v) := by
    rw [← (_root_.FiberBundle.trivializationAt E (TangentSpace I) (x₀ : M)).symmL_apply
      (R := ℝ) hb_ambient]
    exact (_root_.FiberBundle.trivializationAt E (TangentSpace I) (x₀ : M)).symmL_continuousLinearMapAt
      (R := ℝ) hb_ambient (boundaryInclusionMfderiv b ((_root_.FiberBundle.trivializationAt hI.boundaryE
        (TangentSpace hI.boundaryI) x₀).symm b v))
  have hM_w : (_root_.FiberBundle.trivializationAt E (TangentSpace I) (x₀ : M)).symm (b : M)
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) (x₀ : M)).continuousLinearMapAt ℝ (b : M)
          (boundaryInclusionMfderiv b ((_root_.FiberBundle.trivializationAt hI.boundaryE
            (TangentSpace hI.boundaryI) x₀).symm b w)))
      = boundaryInclusionMfderiv b ((_root_.FiberBundle.trivializationAt hI.boundaryE
            (TangentSpace hI.boundaryI) x₀).symm b w) := by
    rw [← (_root_.FiberBundle.trivializationAt E (TangentSpace I) (x₀ : M)).symmL_apply
      (R := ℝ) hb_ambient]
    exact (_root_.FiberBundle.trivializationAt E (TangentSpace I) (x₀ : M)).symmL_continuousLinearMapAt
      (R := ℝ) hb_ambient (boundaryInclusionMfderiv b ((_root_.FiberBundle.trivializationAt hI.boundaryE
        (TangentSpace hI.boundaryI) x₀).symm b w))
  rw [hM_v, hM_w]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetricInner_chart_eval
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetricInner_chart_eval target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private lemma dincl_chart_conjugated_contMDiffAt
    (x₀ : BoundaryManifold I M) :
    ContMDiffAt hI.boundaryI 𝓘(ℝ, hI.boundaryE →L[ℝ] E) ∞
      (fun b : BoundaryManifold I M =>
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) (x₀ : M)).continuousLinearMapAt ℝ (b : M)).comp
          ((boundaryInclusionMfderiv b).comp
            ((_root_.FiberBundle.trivializationAt hI.boundaryE
                (TangentSpace hI.boundaryI) x₀).symmL ℝ b))) x₀ := by
  have h_inclusion_at : ContMDiffAt hI.boundaryI I ∞ (boundaryInclusion I M) x₀ :=
    boundaryInclusion_contMDiff.contMDiffAt
  have h_mfderiv : ContMDiffAt hI.boundaryI 𝓘(ℝ, hI.boundaryE →L[ℝ] E) ∞
      (inTangentCoordinates hI.boundaryI I id (boundaryInclusion I M)
        (mfderiv hI.boundaryI I (boundaryInclusion I M)) x₀) x₀ := by
    have h_top_add : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
      have h_eq : (∞ : WithTop ℕ∞) + 1 = (∞ : WithTop ℕ∞) := by
        rfl
      rw [h_eq]
    exact h_inclusion_at.mfderiv_const h_top_add
  have h_nhds : ∀ᶠ b in 𝓝 x₀,
      inTangentCoordinates hI.boundaryI I id (boundaryInclusion I M)
        (mfderiv hI.boundaryI I (boundaryInclusion I M)) x₀ b
      = ((_root_.FiberBundle.trivializationAt E (TangentSpace I) (x₀ : M)).continuousLinearMapAt ℝ (b : M)).comp
        ((boundaryInclusionMfderiv b).comp
          ((_root_.FiberBundle.trivializationAt hI.boundaryE
              (TangentSpace hI.boundaryI) x₀).symmL ℝ b)) := by
    have h_nhds_amb : ∀ᶠ b : BoundaryManifold I M in 𝓝 x₀,
        (b : M) ∈ (chartAt H (x₀ : M)).source := by
      have h_open : IsOpen ((chartAt H (x₀ : M)).source) := (chartAt H (x₀ : M)).open_source
      have h_x₀_in : (x₀ : M) ∈ (chartAt H (x₀ : M)).source := mem_chart_source H _
      have h_continuous : Continuous (Subtype.val :
          {x : M // x ∈ I.boundary M} → M) := continuous_subtype_val
      have h_continuous_b : Continuous (fun b : BoundaryManifold I M => (b : M)) :=
        continuous_subtype_val
      exact (h_continuous_b.continuousAt.preimage_mem_nhds (h_open.mem_nhds h_x₀_in))
    have h_nhds_bdy : ∀ᶠ b : BoundaryManifold I M in 𝓝 x₀,
        b ∈ (chartAt hI.boundaryH x₀).source := by
      exact (chartAt hI.boundaryH x₀).open_source.mem_nhds (mem_chart_source _ _)
    filter_upwards [h_nhds_amb, h_nhds_bdy] with b h_amb h_bdy
    have h_inT := inTangentCoordinates_eq_mfderiv_comp
      (I := hI.boundaryI) (I' := I) (𝕜 := ℝ)
      (f := id) (g := boundaryInclusion I M)
      (ϕ := mfderiv hI.boundaryI I (boundaryInclusion I M)) (x₀ := x₀) (x := b)
      (hx := h_bdy) (hy := h_amb)
    have h_clmAt_eq : (_root_.FiberBundle.trivializationAt E (TangentSpace I) (x₀ : M)).continuousLinearMapAt ℝ (b : M)
        = mfderiv I 𝓘(ℝ, E) (extChartAt I (x₀ : M)) (b : M) :=
      TangentBundle.continuousLinearMapAt_trivializationAt h_amb
    have h_symmL_eq : (_root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) x₀).symmL ℝ b
        = mfderivWithin 𝓘(ℝ, hI.boundaryE) hI.boundaryI (extChartAt hI.boundaryI x₀).symm
            (Set.range hI.boundaryI) (extChartAt hI.boundaryI x₀ b) :=
      TangentBundle.symmL_trivializationAt h_bdy
    rw [h_inT]
    change _ = ((_root_.FiberBundle.trivializationAt E (TangentSpace I) (x₀ : M)).continuousLinearMapAt ℝ (b : M)).comp
        ((boundaryInclusionMfderiv b).comp ((_root_.FiberBundle.trivializationAt hI.boundaryE
              (TangentSpace hI.boundaryI) x₀).symmL ℝ b))
    rw [h_clmAt_eq, h_symmL_eq]
    rfl
  exact h_mfderiv.congr_of_eventuallyEq h_nhds

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.dincl_chart_conjugated_contMDiffAt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.dincl_chart_conjugated_contMDiffAt target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
theorem inducedMetricInner_contMDiff
    (g : SmoothRiemannianMetric I M) :
    ContMDiff hI.boundaryI
      (hI.boundaryI.prod 𝓘(ℝ, hI.boundaryE →L[ℝ] hI.boundaryE →L[ℝ] ℝ)) ∞
      (fun b : BoundaryManifold I M =>
        TotalSpace.mk' (hI.boundaryE →L[ℝ] hI.boundaryE →L[ℝ] ℝ)
          (E := fun y : BoundaryManifold I M =>
            TangentSpace hI.boundaryI y →L[ℝ] TangentSpace hI.boundaryI y →L[ℝ] ℝ)
          b (inducedMetricInner g b)) := by
  by_cases hN : Nonempty hI.boundaryH
  · have := hN
    intro x₀
    rw [(_root_.FiberBundle.trivializationAt (hI.boundaryE →L[ℝ] hI.boundaryE →L[ℝ] ℝ)
      (fun y : BoundaryManifold I M =>
        TangentSpace hI.boundaryI y →L[ℝ] TangentSpace hI.boundaryI y →L[ℝ] ℝ) x₀).contMDiffAt_section_iff
      (FiberBundle.mem_baseSet_trivializationAt' x₀)]
    have h_gInner_at : ContMDiffAt hI.boundaryI 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
        (fun b : BoundaryManifold I M =>
          gInnerCharted (I := I) (M := M) g (x₀ : M) (b : M)) x₀ :=
      gInnerCharted_along_inclusion_contMDiffAt g x₀
    have h_L_at : ContMDiffAt hI.boundaryI 𝓘(ℝ, hI.boundaryE →L[ℝ] E) ∞
        (fun b : BoundaryManifold I M =>
          ((_root_.FiberBundle.trivializationAt E (TangentSpace I) (x₀ : M)).continuousLinearMapAt ℝ (b : M)).comp
            ((boundaryInclusionMfderiv b).comp
              ((_root_.FiberBundle.trivializationAt hI.boundaryE
                  (TangentSpace hI.boundaryI) x₀).symmL ℝ b))) x₀ :=
      dincl_chart_conjugated_contMDiffAt x₀
    have h_bilinearComp : ContMDiffAt hI.boundaryI 𝓘(ℝ, hI.boundaryE →L[ℝ] hI.boundaryE →L[ℝ] ℝ) ∞
        (fun b : BoundaryManifold I M =>
          (gInnerCharted (I := I) (M := M) g (x₀ : M) (b : M)).bilinearComp
            (((_root_.FiberBundle.trivializationAt E (TangentSpace I) (x₀ : M)).continuousLinearMapAt ℝ (b : M)).comp
              ((boundaryInclusionMfderiv b).comp
                ((_root_.FiberBundle.trivializationAt hI.boundaryE
                    (TangentSpace hI.boundaryI) x₀).symmL ℝ b)))
            (((_root_.FiberBundle.trivializationAt E (TangentSpace I) (x₀ : M)).continuousLinearMapAt ℝ (b : M)).comp
              ((boundaryInclusionMfderiv b).comp
                ((_root_.FiberBundle.trivializationAt hI.boundaryE
                    (TangentSpace hI.boundaryI) x₀).symmL ℝ b)))) x₀ := by
      let ψ := fun b : BoundaryManifold I M =>
        gInnerCharted (I := I) (M := M) g (x₀ : M) (b : M)
      let L := fun b : BoundaryManifold I M =>
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) (x₀ : M)).continuousLinearMapAt ℝ (b : M)).comp
          ((boundaryInclusionMfderiv b).comp
            ((_root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) x₀).symmL ℝ b))
      have hψb : ContMDiffAt hI.boundaryI (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
          (fun b => (⟨0, ψ b⟩ : _root_.Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
            (fun x : ℝ => Bundle.Trivial ℝ E x →L[ℝ] Bundle.Trivial ℝ E x →L[ℝ] Bundle.Trivial ℝ ℝ x))) x₀ := by
        rw [contMDiffAt_hom_bundle]
        refine ⟨contMDiffAt_const, ?_⟩
        apply h_gInner_at.congr_of_eventuallyEq
        apply Filter.Eventually.of_forall
        intro b
        ext v w
        rw [inCoordinates_apply_eq₂ (by simp) (by simp) (by simp)]
        simp [ψ]
      have hLb : ContMDiffAt hI.boundaryI (𝓘(ℝ, ℝ).prod 𝓘(ℝ, hI.boundaryE →L[ℝ] E)) ∞
          (fun b => (⟨0, L b⟩ : _root_.Bundle.TotalSpace (hI.boundaryE →L[ℝ] E)
            (fun x : ℝ => Bundle.Trivial ℝ hI.boundaryE x →L[ℝ] Bundle.Trivial ℝ E x))) x₀ := by
        rw [contMDiffAt_hom_bundle]
        refine ⟨contMDiffAt_const, ?_⟩
        apply h_L_at.congr_of_eventuallyEq
        exact Filter.Eventually.of_forall fun b => by
          simp [ContinuousLinearMap.inCoordinates, L]
      have h := hψb.clm_bundle_bilinearComp
        (F₁ := E) (F₂ := E) (F₃ := ℝ) (F₄ := hI.boundaryE) (F₅ := hI.boundaryE)
        (U₁ := Bundle.Trivial ℝ E) (U₂ := Bundle.Trivial ℝ E) (U₃ := Bundle.Trivial ℝ ℝ)
        (U₄ := Bundle.Trivial ℝ hI.boundaryE) (U₅ := Bundle.Trivial ℝ hI.boundaryE) hLb hLb
      rw [contMDiffAt_hom_bundle] at h
      apply h.2.congr_of_eventuallyEq
      apply Filter.Eventually.of_forall
      intro b
      ext v w
      rw [inCoordinates_apply_eq₂ (by simp) (by simp) (by simp)]
      simp [ψ, L]
    refine h_bilinearComp.congr_of_eventuallyEq ?_
    have h_nhds_amb : ∀ᶠ b : BoundaryManifold I M in 𝓝 x₀,
        (b : M) ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) (x₀ : M)).baseSet := by
      have h_open : IsOpen ((_root_.FiberBundle.trivializationAt E (TangentSpace I) (x₀ : M)).baseSet) :=
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) (x₀ : M)).open_baseSet
      have h_x₀_in : (x₀ : M) ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) (x₀ : M)).baseSet :=
        FiberBundle.mem_baseSet_trivializationAt' (x₀ : M)
      have h_continuous : Continuous (fun b : BoundaryManifold I M => (b : M)) :=
        continuous_subtype_val
      exact (h_continuous.continuousAt.preimage_mem_nhds (h_open.mem_nhds h_x₀_in))
    have h_nhds_bdy : ∀ᶠ b : BoundaryManifold I M in 𝓝 x₀,
        b ∈ (_root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) x₀).baseSet := by
      have h_open : IsOpen ((_root_.FiberBundle.trivializationAt hI.boundaryE
        (TangentSpace hI.boundaryI) x₀).baseSet) :=
        (_root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) x₀).open_baseSet
      have h_x₀_in : x₀ ∈ (_root_.FiberBundle.trivializationAt hI.boundaryE
        (TangentSpace hI.boundaryI) x₀).baseSet :=
        FiberBundle.mem_baseSet_trivializationAt' x₀
      exact h_open.mem_nhds h_x₀_in
    filter_upwards [h_nhds_amb, h_nhds_bdy] with b hb_amb hb_bdy
    refine ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => ?_
    rw [ContinuousLinearMap.bilinearComp_apply]
    rw [inducedMetricInner_chart_eval g x₀ b hb_amb hb_bdy v w]
    change _ = (gInnerCharted (I := I) (M := M) g (x₀ : M) (b : M))
      ((_root_.FiberBundle.trivializationAt E (TangentSpace I) (x₀ : M)).continuousLinearMapAt ℝ (b : M)
        (boundaryInclusionMfderiv b
          ((_root_.FiberBundle.trivializationAt hI.boundaryE
            (TangentSpace hI.boundaryI) x₀).symmL ℝ b v)))
      ((_root_.FiberBundle.trivializationAt E (TangentSpace I) (x₀ : M)).continuousLinearMapAt ℝ (b : M)
        (boundaryInclusionMfderiv b
          ((_root_.FiberBundle.trivializationAt hI.boundaryE
            (TangentSpace hI.boundaryI) x₀).symmL ℝ b w)))
    rw [(_root_.FiberBundle.trivializationAt hI.boundaryE
      (TangentSpace hI.boundaryI) x₀).symmL_apply (R := ℝ) hb_bdy]
    rw [(_root_.FiberBundle.trivializationAt hI.boundaryE
      (TangentSpace hI.boundaryI) x₀).symmL_apply (R := ℝ) hb_bdy]
  · have : IsEmpty hI.boundaryH := not_nonempty_iff.mp hN
    have : IsEmpty (BoundaryManifold I M) :=
      BoundaryManifold.isEmpty_of_isEmpty_boundaryH (I := I)
    intro x; exact (IsEmpty.false x).elim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetricInner_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetricInner_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetricInner_contMDiff ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetricInner_contMDiff

noncomputable def inducedMetric
    (g : SmoothRiemannianMetric I M) :
    SmoothRiemannianMetric hI.boundaryI (BoundaryManifold I M) where
  inner := inducedMetricInner g
  symm := inducedMetricInner_symm g
  pos := inducedMetricInner_pos g
  isVonNBounded := inducedMetricInner_isVonNBounded g
  contMDiff := inducedMetricInner_contMDiff g

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetric ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetric

omit [FiniteDimensional ℝ E] in
@[simp] lemma inducedMetric_inner
    (g : SmoothRiemannianMetric I M) (b : BoundaryManifold I M) :
    (inducedMetric g).inner b = inducedMetricInner g b := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetric_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetric_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetric_inner ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetric_inner

omit [FiniteDimensional ℝ E] in
lemma inducedMetric_inner_apply
    (g : SmoothRiemannianMetric I M) (b : BoundaryManifold I M)
    (v w : TangentSpace hI.boundaryI b) :
    (inducedMetric g).inner b v w = g.inner (b : M) (boundaryInclusionMfderiv b v)
      (boundaryInclusionMfderiv b w) :=
  inducedMetricInner_apply g b v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetric_inner_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetric_inner_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetric_inner_apply ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetric_inner_apply

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
