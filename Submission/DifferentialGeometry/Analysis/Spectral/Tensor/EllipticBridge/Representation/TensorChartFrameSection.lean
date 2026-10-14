import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.WeakSolution.WeakSolutionHeadline
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.Representation.TensorReprFromFrame

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.BigOperators _root_.Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral


open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartLocalLaplacian
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid

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

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [T2Space M]
    [SigmaCompactSpace M] in
private lemma component_contDiff_of_contDiffOn (α : M)
    {f : EuclN → ℝ}
    (hf : ContDiffOn ℝ ∞ f (chartTargetEuclid (I := I) (M := M) α))
    (hf_support : tsupport f ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ContDiff ℝ ∞ f :=
  contDiff_of_contDiffOn_chartTarget_zero_off (I := I) (M := M) α
    (isClosed_tsupport f) hf_support hf
    (fun _ hy => image_eq_zero_of_notMem_tsupport hy)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.component_contDiff_of_contDiffOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.component_contDiff_of_contDiffOn target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma componentBump_contMDiffOn
    (α : M) {f : EuclN → ℝ}
    (hf : ContDiffOn ℝ ∞ f (chartTargetEuclid (I := I) (M := M) α))
    (hf_support : tsupport f ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (chartTestPullback (I := I) α f)
      (chartAt H α).source :=
  chartTestPullback_contMDiffOn (I := I) (M := M) α
    (component_contDiff_of_contDiffOn (I := I) (M := M) α hf hf_support)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.componentBump_contMDiffOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.componentBump_contMDiffOn target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
    [SigmaCompactSpace M] in
private lemma componentBump_tsupport_subset
    (α : M) {f : EuclN → ℝ}
    (hf_cs : HasCompactSupport f)
    (hf_support : tsupport f ⊆ chartTargetEuclid (I := I) (M := M) α) :
    tsupport (chartTestPullback (I := I) α f) ⊆ (chartAt H α).source :=
  chartTestPullback_tsupport_subset_source (I := I) (M := M) α hf_cs hf_support

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.componentBump_tsupport_subset
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.componentBump_tsupport_subset target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma tensorTrivProj_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {ι : Type*} (t : Finset ι) (S : ι → SmoothCcTensor g r s) (b : M) :
    tensorTrivProj (I := I) (M := M) g r s (∑ i ∈ t, S i) α b =
      ∑ i ∈ t, tensorTrivProj (I := I) (M := M) g r s (S i) α b := by
  classical
  have hadd : ∀ S₁ S₂ : SmoothCcTensor g r s,
      tensorTrivProj (I := I) (M := M) g r s (S₁ + S₂) α b =
        tensorTrivProj (I := I) (M := M) g r s S₁ α b +
          tensorTrivProj (I := I) (M := M) g r s S₂ α b := by
    intro S₁ S₂
    unfold tensorTrivProj
    rw [show (S₁ + S₂).toSection b = S₁.toSection b + S₂.toSection b from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    exact ContinuousLinearMap.map_add _ _ _
  have hzero : tensorTrivProj (I := I) (M := M) g r s
      (0 : SmoothCcTensor g r s) α b = 0 := by
    unfold tensorTrivProj
    rw [show (0 : SmoothCcTensor g r s).toSection b = 0 from by
      rw [SmoothCcTensor.toSection_zero]; rfl]
    exact ContinuousLinearMap.map_zero _
  induction t using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, hzero]
  | insert i A hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hadd, ih]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorTrivProj_sum
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorTrivProj_sum target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma tensorChartComponentRaw_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {ι : Type*} (t : Finset ι) (S : ι → SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) (b : M) :
    tensorChartComponentRaw (I := I) (M := M) g r s (∑ i ∈ t, S i)
        α Idx Jdx b =
      ∑ i ∈ t, tensorChartComponentRaw (I := I) (M := M) g r s (S i)
        α Idx Jdx b := by
  classical
  unfold tensorChartComponentRaw
  rw [tensorTrivProj_sum (I := I) (M := M) g r s α t S b]
  exact map_sum (tensorChartComponentProjection (E := E) r s Idx Jdx) _ _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_sum
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_sum target :: scope.openDecls } }

noncomputable def tensorBundleSectionOfChartComponents
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (u : TensorCompIdx (E := E) r s → EuclN → ℝ)
    (hu : ∀ P, ContDiffOn ℝ ∞ (u P)
      (chartTargetEuclid (I := I) (M := M) α))
    (hsupp : ∀ P, HasCompactSupport (u P) ∧
      tsupport (u P) ⊆ chartTargetEuclid (I := I) (M := M) α) :
    SmoothCcTensor g r s := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  classical
  exact
    ∑ P : TensorCompIdx (E := E) r s,
      chartBasisTensorSection (I := I) (M := M) g r s α
        (chartTestPullback (I := I) α (u P))
        (componentBump_contMDiffOn (I := I) (M := M) α (hu P) (hsupp P).2)
        (componentBump_tsupport_subset (I := I) (M := M) α
          (hsupp P).1 (hsupp P).2)
        P

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorBundleSectionOfChartComponents then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorBundleSectionOfChartComponents"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorBundleSectionOfChartComponents ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorBundleSectionOfChartComponents

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma tensorBundleSectionOfChartComponents_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (u : TensorCompIdx (E := E) r s → EuclN → ℝ)
    (hu : ∀ P, ContDiffOn ℝ ∞ (u P)
      (chartTargetEuclid (I := I) (M := M) α))
    (hsupp : ∀ P, HasCompactSupport (u P) ∧
      tsupport (u P) ⊆ chartTargetEuclid (I := I) (M := M) α) :
    tensorBundleSectionOfChartComponents (I := I) (M := M) g r s α u hu hsupp =
      ∑ P : TensorCompIdx (E := E) r s,
        chartBasisTensorSection (I := I) (M := M) g r s α
          (chartTestPullback (I := I) α (u P))
          (componentBump_contMDiffOn (I := I) (M := M) α (hu P) (hsupp P).2)
          (componentBump_tsupport_subset (I := I) (M := M) α
            (hsupp P).1 (hsupp P).2)
          P := by
  classical
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorBundleSectionOfChartComponents_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorBundleSectionOfChartComponents_eq target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem tensorBundleSectionOfChartComponents_toSection_eq_zero_off_source
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (u : TensorCompIdx (E := E) r s → EuclN → ℝ)
    (hu : ∀ P, ContDiffOn ℝ ∞ (u P)
      (chartTargetEuclid (I := I) (M := M) α))
    (hsupp : ∀ P, HasCompactSupport (u P) ∧
      tsupport (u P) ⊆ chartTargetEuclid (I := I) (M := M) α)
    {x : M} (hx : x ∉ (chartAt H α).source) :
    (tensorBundleSectionOfChartComponents (I := I) (M := M) g r s α
        u hu hsupp).toSection x = 0 := by
  classical
  rw [tensorBundleSectionOfChartComponents_eq (I := I) (M := M) g r s α u hu hsupp]
  set S : TensorCompIdx (E := E) r s → SmoothCcTensor g r s :=
    fun P => chartBasisTensorSection (I := I) (M := M) g r s α
      (chartTestPullback (I := I) α (u P))
      (componentBump_contMDiffOn (I := I) (M := M) α (hu P) (hsupp P).2)
      (componentBump_tsupport_subset (I := I) (M := M) α
        (hsupp P).1 (hsupp P).2) P with hS_def
  have h_sum_section :
      (∑ P : TensorCompIdx (E := E) r s, S P).toSection =
        ∑ P : TensorCompIdx (E := E) r s, (S P).toSection :=
    map_sum (SmoothCcTensor.toSectionAddHom (I := I) (M := M) (g := g)
      (r := r) (s := s)) _ _
  have h_coe : ⇑(∑ P : TensorCompIdx (E := E) r s, (S P).toSection) =
      ∑ P : TensorCompIdx (E := E) r s, ⇑(S P).toSection :=
    map_sum (ContMDiffSection.coeAddHom I (TensorRSModel r s ℝ E) ∞
      (fun b : M => TensorRSSpace r s I b)) _ _
  have h_eval : (∑ P : TensorCompIdx (E := E) r s, S P).toSection x =
      ∑ P : TensorCompIdx (E := E) r s, (S P).toSection x := by
    rw [h_sum_section]
    have := congrFun h_coe x
    rw [Finset.sum_apply] at this
    exact this
  rw [h_eval]
  refine Finset.sum_eq_zero (fun P _ => ?_)
  rw [hS_def, chartBasisTensorSection_toSection_apply (I := I) (M := M) g r s α
    (componentBump_contMDiffOn (I := I) (M := M) α (hu P) (hsupp P).2)
    (componentBump_tsupport_subset (I := I) (M := M) α
      (hsupp P).1 (hsupp P).2) P x,
    chartTestPullback_apply_of_notMem (I := I) α _ hx, zero_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorBundleSectionOfChartComponents_toSection_eq_zero_off_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorBundleSectionOfChartComponents_toSection_eq_zero_off_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorBundleSectionOfChartComponents_toSection_eq_zero_off_source ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorBundleSectionOfChartComponents_toSection_eq_zero_off_source

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem tensorChartComponentRaw_tensorBundleSectionOfChartComponents
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (u : TensorCompIdx (E := E) r s → EuclN → ℝ)
    (hu : ∀ P, ContDiffOn ℝ ∞ (u P)
      (chartTargetEuclid (I := I) (M := M) α))
    (hsupp : ∀ P, HasCompactSupport (u P) ∧
      tsupport (u P) ⊆ chartTargetEuclid (I := I) (M := M) α)
    (P : TensorCompIdx (E := E) r s)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorChartComponentRaw (I := I) (M := M) g r s
        (tensorBundleSectionOfChartComponents (I := I) (M := M) g r s α
          u hu hsupp)
        α P.1 P.2 ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
      u P y := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  classical
  rw [tensorBundleSectionOfChartComponents_eq (I := I) (M := M) g r s α
    u hu hsupp]
  rw [tensorChartComponentRaw_sum (I := I) (M := M) g r s α Finset.univ _
    P.1 P.2 ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))]
  have hterm : ∀ Q : TensorCompIdx (E := E) r s,
      tensorChartComponentRaw (I := I) (M := M) g r s
          (chartBasisTensorSection (I := I) (M := M) g r s α
            (chartTestPullback (I := I) α (u Q))
            (componentBump_contMDiffOn (I := I) (M := M) α (hu Q) (hsupp Q).2)
            (componentBump_tsupport_subset (I := I) (M := M) α
              (hsupp Q).1 (hsupp Q).2)
            Q)
          α P.1 P.2 ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
        chartPushedRaw I α (chartTestPullback (I := I) α (u Q)) y *
          (if (P.1, P.2) = Q then (1 : ℝ) else 0) :=
    fun Q => chartBasisTensorSection_chartComp (I := I) (M := M) g r s α
      (componentBump_contMDiffOn (I := I) (M := M) α (hu Q) (hsupp Q).2)
      (componentBump_tsupport_subset (I := I) (M := M) α
        (hsupp Q).1 (hsupp Q).2)
      Q P.1 P.2 hy
  rw [Finset.sum_congr rfl (fun Q _ => hterm Q)]
  rw [Finset.sum_eq_single P]
  · rw [show ((P.1, P.2) : TensorCompIdx (E := E) r s) = P from Prod.ext rfl rfl]
    rw [if_pos rfl, mul_one]
    exact chartPushedRaw_chartTestPullback_eqOn (I := I) (M := M) α (u P) hy
  · intro Q _ hne
    rw [show ((P.1, P.2) : TensorCompIdx (E := E) r s) = P from Prod.ext rfl rfl]
    rw [if_neg (fun h => hne h.symm), _root_.MulZeroClass.mul_zero]
  · intro hP
    exact absurd (Finset.mem_univ P) hP

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_tensorBundleSectionOfChartComponents then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_tensorBundleSectionOfChartComponents"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_tensorBundleSectionOfChartComponents ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_tensorBundleSectionOfChartComponents

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
