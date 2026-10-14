import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.WeakSolution.WeakSolutionHeadline
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.Representation.TensorReprFromFrame

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.MeasureTheory
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators _root_.Matrix
open _root_.Submission.DifferentialGeometry.Tensor0SBundle

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral


open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

noncomputable def pouSmul
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) : SmoothCcTensor g r s where
  toSection :=
    { toFun := fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x • S.toSection x
      contMDiff_toFun := by
        exact ContMDiff.smul_section
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff S.toSection.contMDiff }
  hasCompactSupport := by
    classical
    refine HasCompactSupport.of_support_subset_isCompact S.hasCompactSupport ?_
    intro x hx
    rw [Function.mem_support] at hx
    refine subset_tsupport S.toFun ?_
    rw [Function.mem_support]
    intro hS_zero
    apply hx
    change TensorRSSpace.toModel
      (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x • S.toSection x) = 0
    rw [TensorRSSpace.toModel_smul,
      show TensorRSSpace.toModel (S.toSection x) = S.toFun x from rfl, hS_zero,
      smul_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouSmul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouSmul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouSmul ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouSmul

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
lemma pouSmul_toSection_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) (x : M) :
    (pouSmul (I := I) (M := M) g r s α S).toSection x =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x • S.toSection x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouSmul_toSection_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouSmul_toSection_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouSmul_toSection_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouSmul_toSection_apply

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma pouSmul_toFun_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) (x : M) :
    (pouSmul (I := I) (M := M) g r s α S).toFun x =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x • S.toFun x := by
  rw [SmoothCcTensor.toFun_apply, pouSmul_toSection_apply,
    TensorRSSpace.toModel_smul]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouSmul_toFun_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouSmul_toFun_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouSmul_toFun_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouSmul_toFun_apply

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma tensorTrivProj_pouSmul
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) (x : M) :
    tensorTrivProj (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α S) α x =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x •
        tensorTrivProj (I := I) (M := M) g r s S α x := by
  unfold tensorTrivProj
  rw [pouSmul_toSection_apply]
  exact ContinuousLinearMap.map_smul _ _ _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorTrivProj_pouSmul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorTrivProj_pouSmul target :: scope.openDecls } }

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem tensorChartComponentRaw_smul_pou
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComponentRaw (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α S) α Idx Jdx =
      fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
        tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx x := by
  funext x
  unfold tensorChartComponentRaw
  rw [tensorTrivProj_pouSmul (I := I) (M := M) g r s α S x, ContinuousLinearMap.map_smul,
    smul_eq_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_smul_pou then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_smul_pou"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_smul_pou ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_smul_pou

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem tensorChartComponentRaw_pouSmul_eq_tensorChartComponentPou
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComponentRaw (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α S) α Idx Jdx =
      tensorChartComponentPou (I := I) (M := M) g r s S α Idx Jdx := by
  rw [tensorChartComponentRaw_smul_pou (I := I) (M := M) g r s α S Idx Jdx]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_pouSmul_eq_tensorChartComponentPou then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_pouSmul_eq_tensorChartComponentPou"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_pouSmul_eq_tensorChartComponentPou ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_pouSmul_eq_tensorChartComponentPou

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem pouSmul_tsupport_subset_chartSource
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) :
    tsupport (pouSmul (I := I) (M := M) g r s α S).toFun ⊆
      (chartAt H α).source := by
  classical
  have hfun_eq : (pouSmul (I := I) (M := M) g r s α S).toFun =
      fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x •
        S.toFun x := by
    funext x
    exact pouSmul_toFun_apply (I := I) (M := M) g r s α S x
  rw [hfun_eq]
  have h_support_sub : Function.support
      (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x •
        S.toFun x) ⊆
      Function.support
        (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) := by
    intro x hx
    rw [Function.mem_support] at hx ⊢
    intro hweight_zero
    exact hx (by rw [hweight_zero, zero_smul])
  refine (closure_mono h_support_sub).trans ?_
  exact (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate
    I M) α

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouSmul_tsupport_subset_chartSource then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouSmul_tsupport_subset_chartSource"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouSmul_tsupport_subset_chartSource ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouSmul_tsupport_subset_chartSource

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem tensorChartComponent_eq_tensorComponentEuclid_pouSmul
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) (P₀ : CompIdx E r s) :
    tensorChartComponent (I := I) (M := M) g r s S α P₀.1 P₀.2 =
      tensorComponentEuclid (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α S) α P₀ := by
  rw [tensorComponentEuclid_def, tensorChartComponent_def,
    tensorChartComponentRaw_pouSmul_eq_tensorChartComponentPou
      (I := I) (M := M) g r s α S P₀.1 P₀.2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_eq_tensorComponentEuclid_pouSmul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_eq_tensorComponentEuclid_pouSmul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_eq_tensorComponentEuclid_pouSmul ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_eq_tensorComponentEuclid_pouSmul

theorem tensorChartComponent_isSmoothWeakSolution
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S F : SmoothCcTensor g r s) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (P₀ : CompIdx E r s)
    (hF_support : tsupport F.toFun ⊆ (chartAt H α).source)
    (hS_K : tsupport
        (tensorChartComponent (I := I) (M := M) g r s S α P₀.1 P₀.2) ⊆ K)
    (hweak : ∀ v : SmoothCcTensor g r s,
      ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s
            (pouSmul (I := I) (M := M) g r s α S) v x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        tensorL2Inner (I := I) (M := M) g r s F.toFun v.toFun) :
    (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).IsSmoothWeakSolution
      (tensorChartComponent (I := I) (M := M) g r s S α P₀.1 P₀.2)
      (tensorComponentWeakRHS (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α S) F α P₀) := by
  classical
  have hcomp_eq :
      tensorChartComponent (I := I) (M := M) g r s S α P₀.1 P₀.2 =
        tensorComponentEuclid (I := I) (M := M) g r s
          (pouSmul (I := I) (M := M) g r s α S) α P₀ :=
    tensorChartComponent_eq_tensorComponentEuclid_pouSmul
      (I := I) (M := M) g r s α S P₀
  have hpou_support :
      tsupport (pouSmul (I := I) (M := M) g r s α S).toFun ⊆
        (chartAt H α).source :=
    pouSmul_tsupport_subset_chartSource (I := I) (M := M) g r s α S
  have hpou_K :
      tsupport (tensorComponentEuclid (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α S) α P₀) ⊆ K := by
    rw [← hcomp_eq]; exact hS_K
  rw [hcomp_eq]
  exact tensorComponent_isSmoothWeakSolution (I := I) (M := M) g r s
    (pouSmul (I := I) (M := M) g r s α S) F α hK hK_target P₀
    hpou_support hF_support hpou_K hweak

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_isSmoothWeakSolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_isSmoothWeakSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_isSmoothWeakSolution ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_isSmoothWeakSolution

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
