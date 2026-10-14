import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.WeakSolution.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.MeasureTheory
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators _root_.Matrix
open _root_.Submission.DifferentialGeometry.Tensor0SBundle

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace TensorRegularity


open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

noncomputable def sourcePairingCoeff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s) : EuclN → ℝ :=
  fun y =>
    ∑ Q : CompIdx E r s,
      covChartMetricGramInv (I := I) (M := M) g r s α y Q P₀ *
        ∑ P : CompIdx E r s,
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            tensorComponentEuclid (I := I) (M := M) g r s F α P y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.sourcePairingCoeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.sourcePairingCoeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.sourcePairingCoeff ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.sourcePairingCoeff

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
lemma sourcePairingCoeff_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s) (y : EuclN) :
    sourcePairingCoeff (I := I) (M := M) g r s F α P₀ y =
      ∑ Q : CompIdx E r s,
        covChartMetricGramInv (I := I) (M := M) g r s α y Q P₀ *
          ∑ P : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
              tensorComponentEuclid (I := I) (M := M) g r s F α P y := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.sourcePairingCoeff_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.sourcePairingCoeff_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.sourcePairingCoeff_def ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.sourcePairingCoeff_def

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem sourcePairingCoeff_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s) :
    ContDiffOn ℝ ∞ (sourcePairingCoeff (I := I) (M := M) g r s F α P₀)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  refine ContDiffOn.sum (fun Q _ => ?_)
  refine ContDiffOn.mul ?_ ?_
  · exact covChartMetricGramInv_entry_contDiffOn (I := I) (M := M) g r s α Q P₀
  · refine ContDiffOn.sum (fun P _ => ?_)
    refine ContDiffOn.mul ?_ ?_
    · exact covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q
    · exact tensorComponentEuclid_contDiffOn (I := I) (M := M) g r s F α P

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.sourcePairingCoeff_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.sourcePairingCoeff_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.sourcePairingCoeff_contDiffOn ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.sourcePairingCoeff_contDiffOn

private noncomputable def rotatedSummandBump
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ Q : CompIdx E r s) (χ : M → ℝ) : M → ℝ :=
  fun b => gramInvWeight (I := I) (M := M) g r s α P₀ Q b * χ b

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.rotatedSummandBump
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.rotatedSummandBump target :: scope.openDecls } }

private noncomputable def rotatedSummand
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source)
    (Q : CompIdx E r s) : SmoothCcTensor g r s :=
  chartBasisTensorSection (I := I) (M := M) g r s α
    (rotatedSummandBump (I := I) (M := M) g r s α P₀ Q χ)
    (gramInvWeight_mul_bump_contMDiffOn (I := I) (M := M) g r s α P₀ Q hχs)
    (gramInvWeight_mul_bump_tsupport (I := I) (M := M) g r s α P₀ Q hχt)
    Q

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.rotatedSummand
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.rotatedSummand target :: scope.openDecls } }

omit [CompleteSpace E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma rotatedTestSection_eq_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source) :
    rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt =
      ∑ Q : CompIdx E r s,
        rotatedSummand (I := I) (M := M) g r s α P₀ hχs hχt Q := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.rotatedTestSection_eq_sum
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.rotatedTestSection_eq_sum target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma smoothCcTensor_finsetSum_toFun_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {ι : Type*} (t : Finset ι) (S : ι → SmoothCcTensor g r s) (x : M) :
    (∑ i ∈ t, S i).toFun x = ∑ i ∈ t, (S i).toFun x := by
  classical
  induction t using Finset.induction with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty, SmoothCcTensor.toFun_zero,
        Pi.zero_apply]
  | insert i A hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        SmoothCcTensor.toFun_add, Pi.add_apply, ih]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.smoothCcTensor_finsetSum_toFun_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.smoothCcTensor_finsetSum_toFun_apply target :: scope.openDecls } }

omit [CompleteSpace E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma rotatedTestSection_toFun_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source) (x : M) :
    (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt).toFun x =
      ∑ Q : CompIdx E r s,
        (rotatedSummand (I := I) (M := M) g r s α P₀ hχs hχt Q).toFun x := by
  rw [rotatedTestSection_eq_sum (I := I) (M := M) g r s α P₀ hχs hχt]
  exact smoothCcTensor_finsetSum_toFun_apply (I := I) (M := M) g r s
    Finset.univ _ x

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.rotatedTestSection_toFun_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.rotatedTestSection_toFun_apply target :: scope.openDecls } }

omit [CompleteSpace E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma rotatedSummand_toFun_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source)
    (Q : CompIdx E r s) (x : M) :
    (rotatedSummand (I := I) (M := M) g r s α P₀ hχs hχt Q).toFun x =
      TensorRSSpace.toModel
        (rotatedSummandBump (I := I) (M := M) g r s α P₀ Q χ x •
          chartBasisFiberSection (I := I) (M := M) r s α Q x) := by
  unfold rotatedSummand rotatedSummandBump
  rw [SmoothCcTensor.toFun_apply,
    chartBasisTensorSection_toSection_apply (I := I) (M := M) g r s α
      (gramInvWeight_mul_bump_contMDiffOn (I := I) (M := M) g r s α P₀ Q hχs)
      (gramInvWeight_mul_bump_tsupport (I := I) (M := M) g r s α P₀ Q hχt) Q x]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.rotatedSummand_toFun_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.rotatedSummand_toFun_apply target :: scope.openDecls } }

omit [CompleteSpace E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma rotatedSummand_toFun_eq_zero_of_bump_eq_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source)
    (Q : CompIdx E r s) {x : M} (hx : χ x = 0) :
    (rotatedSummand (I := I) (M := M) g r s α P₀ hχs hχt Q).toFun x = 0 := by
  rw [rotatedSummand_toFun_apply (I := I) (M := M) g r s α P₀ hχs hχt Q x]
  have hbump : rotatedSummandBump (I := I) (M := M) g r s α P₀ Q χ x = 0 := by
    unfold rotatedSummandBump
    rw [hx, _root_.MulZeroClass.mul_zero]
  rw [hbump, zero_smul, TensorRSSpace.toModel_zero]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.rotatedSummand_toFun_eq_zero_of_bump_eq_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.rotatedSummand_toFun_eq_zero_of_bump_eq_zero target :: scope.openDecls } }

omit [CompleteSpace E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma rotatedTestSection_toFun_eq_zero_of_bump_eq_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source)
    {x : M} (hx : χ x = 0) :
    (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt).toFun x = 0 := by
  classical
  rw [rotatedTestSection_toFun_apply (I := I) (M := M) g r s α P₀ hχs hχt x]
  refine Finset.sum_eq_zero (fun Q _ => ?_)
  exact rotatedSummand_toFun_eq_zero_of_bump_eq_zero (I := I) (M := M)
    g r s α P₀ hχs hχt Q hx

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.rotatedTestSection_toFun_eq_zero_of_bump_eq_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.rotatedTestSection_toFun_eq_zero_of_bump_eq_zero target :: scope.openDecls } }

omit [CompleteSpace E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma sourcePairingIntegrand_eq_zero_of_bump_eq_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source)
    {x : M} (hx : χ x = 0) :
    tensorInnerPointwise (I := I) (M := M) g r s x (F.toFun x)
        ((rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt).toFun x) =
      0 := by
  rw [rotatedTestSection_toFun_eq_zero_of_bump_eq_zero (I := I) (M := M)
    g r s α P₀ hχs hχt hx]
  exact tensorInnerPointwise_zero_right (I := I) (M := M) g r s x (F.toFun x)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.sourcePairingIntegrand_eq_zero_of_bump_eq_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.sourcePairingIntegrand_eq_zero_of_bump_eq_zero target :: scope.openDecls } }

omit [CompleteSpace E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma sourcePairingIntegrand_tsupport_subset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source) :
    tsupport
        (fun x : M =>
          tensorInnerPointwise (I := I) (M := M) g r s x (F.toFun x)
            ((rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt).toFun
              x)) ⊆
      (chartAt H α).source := by
  refine (closure_minimal ?_ (isClosed_tsupport χ)).trans hχt
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hx_notsupp
  exact hx (sourcePairingIntegrand_eq_zero_of_bump_eq_zero (I := I) (M := M)
    g r s F α P₀ hχs hχt
    (image_eq_zero_of_notMem_tsupport hx_notsupp))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.sourcePairingIntegrand_tsupport_subset
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.sourcePairingIntegrand_tsupport_subset target :: scope.openDecls } }

omit [CompleteSpace E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma sourcePairingIntegrand_continuous
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source) :
    Continuous
      (fun x : M =>
        tensorInnerPointwise (I := I) (M := M) g r s x (F.toFun x)
          ((rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt).toFun
            x)) :=
  DifferentialGeometry.Integral.L2.SmoothCcTensor.continuous_inner_cross
    (I := I) (M := M)
    F (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.sourcePairingIntegrand_continuous
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.sourcePairingIntegrand_continuous target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma wrappedComponentProj_F_section_eq_tensorChartComponentRaw
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : SmoothCcTensor g r s) (α : M) (b : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    wrappedComponentProj (I := I) (M := M) r s α b Idx Jdx (F.toSection b) =
      tensorChartComponentRaw (I := I) (M := M) g r s F α Idx Jdx b := by
  rw [wrappedComponentProj_apply, tensorChartComponentRaw_def]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.wrappedComponentProj_F_section_eq_tensorChartComponentRaw
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.wrappedComponentProj_F_section_eq_tensorChartComponentRaw target :: scope.openDecls } }

omit [CompleteSpace E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma wrappedComponentProj_rotatedSummand_section
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source)
    (Q : CompIdx E r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    wrappedComponentProj (I := I) (M := M) r s α
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) Idx Jdx
        ((rotatedSummand (I := I) (M := M) g r s α P₀ hχs hχt Q).toSection
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) =
      chartPushedRaw I α (rotatedSummandBump (I := I) (M := M) g r s α P₀ Q χ)
          y *
        (if (Idx, Jdx) = Q then (1 : ℝ) else 0) := by
  rw [wrappedComponentProj_apply]
  rw [show tensorChartComponentProjection (E := E) r s Idx Jdx
        ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
            (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          ((rotatedSummand (I := I) (M := M) g r s α P₀ hχs hχt Q).toSection
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))) =
      tensorChartComponentRaw (I := I) (M := M) g r s
          (rotatedSummand (I := I) (M := M) g r s α P₀ hχs hχt Q) α Idx Jdx
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) from rfl]
  exact chartBasisTensorSection_chartComp (I := I) (M := M) g r s α
    (gramInvWeight_mul_bump_contMDiffOn (I := I) (M := M) g r s α P₀ Q hχs)
    (gramInvWeight_mul_bump_tsupport (I := I) (M := M) g r s α P₀ Q hχt)
    Q Idx Jdx hy

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.wrappedComponentProj_rotatedSummand_section
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.wrappedComponentProj_rotatedSummand_section target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma chartPushedRaw_rotatedSummandBump_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ Q : CompIdx E r s) {χ : M → ℝ}
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushedRaw I α (rotatedSummandBump (I := I) (M := M) g r s α P₀ Q χ) y =
      covChartMetricGramInv (I := I) (M := M) g r s α y Q P₀ *
        chartPushedRaw I α χ y := by
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
  unfold rotatedSummandBump
  have hb_eq : (toEuclidean (E := E))
      ((extChartAt I α)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) = y := by
    have hy' : y ∈ (toEuclidean (E := E)).symm ⁻¹' (extChartAt I α).target := by
      rw [← chartTargetEuclid_eq_preimage_symm (I := I) (M := M)]; exact hy
    rw [(extChartAt I α).right_inv hy', ContinuousLinearEquiv.apply_symm_apply]
  rw [show gramInvWeight (I := I) (M := M) g r s α P₀ Q
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
      covChartMetricGramInv (I := I) (M := M) g r s α y Q P₀ from by
    unfold gramInvWeight; rw [hb_eq]]
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α χ hy]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.chartPushedRaw_rotatedSummandBump_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.chartPushedRaw_rotatedSummandBump_eq target :: scope.openDecls } }

omit [CompleteSpace E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma tensorInnerPointwise_F_rotatedSummand_chart
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source)
    (Q : CompIdx E r s)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorInnerPointwise (I := I) (M := M) g r s
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        (F.toFun ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        ((rotatedSummand (I := I) (M := M) g r s α P₀ hχs hχt Q).toFun
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) =
      covChartMetricGramInv (I := I) (M := M) g r s α y Q P₀ *
        chartPushedRaw I α χ y *
        ∑ P : CompIdx E r s,
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            tensorComponentEuclid (I := I) (M := M) g r s F α P y := by
  classical
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hb_chart : b ∈ (chartAt H α).source :=
    symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  rw [show F.toFun b = TensorRSSpace.toModel (F.toSection b) from rfl]
  rw [show (rotatedSummand (I := I) (M := M) g r s α P₀ hχs hχt Q).toFun b =
      TensorRSSpace.toModel
        ((rotatedSummand (I := I) (M := M) g r s α P₀ hχs hχt Q).toSection b)
      from rfl]
  rw [tensorInnerPointwise_toModel_eq_component_sum (I := I) (M := M)
    g r s α hb_chart (F.toSection b)
    ((rotatedSummand (I := I) (M := M) g r s α P₀ hχs hχt Q).toSection b)]
  have hterm : ∀ P Q' : CompIdx E r s,
      chartTensorInnerPointwiseRsModel (I := I) (M := M) g r s α b
            (tensorChartBasisElement (E := E) r s P.1 P.2)
            (tensorChartBasisElement (E := E) r s Q'.1 Q'.2) *
          (wrappedComponentProj (I := I) (M := M) r s α b P.1 P.2
              (F.toSection b) *
            wrappedComponentProj (I := I) (M := M) r s α b Q'.1 Q'.2
              ((rotatedSummand (I := I) (M := M) g r s α P₀ hχs hχt Q).toSection
                b)) =
        covChartMetricGram (I := I) (M := M) g r s α P Q' y *
          (tensorComponentEuclid (I := I) (M := M) g r s F α P y *
            (chartPushedRaw I α
                (rotatedSummandBump (I := I) (M := M) g r s α P₀ Q χ) y *
              (if (Q'.1, Q'.2) = Q then (1 : ℝ) else 0))) := by
    intro P Q'
    rw [show chartTensorInnerPointwiseRsModel (I := I) (M := M) g r s α b
          (tensorChartBasisElement (E := E) r s P.1 P.2)
          (tensorChartBasisElement (E := E) r s Q'.1 Q'.2) =
        covChartMetricGram (I := I) (M := M) g r s α P Q' y from by
      rw [covChartMetricGram_def, ← hb_def]]
    rw [wrappedComponentProj_F_section_eq_tensorChartComponentRaw
      (I := I) (M := M) g r s F α b P.1 P.2]
    rw [show tensorChartComponentRaw (I := I) (M := M) g r s F α P.1 P.2 b =
        tensorComponentEuclid (I := I) (M := M) g r s F α P y from by
      rw [tensorComponentEuclid_apply_of_mem (I := I) (M := M) g r s F α P hy,
        hb_def]]
    rw [wrappedComponentProj_rotatedSummand_section (I := I) (M := M)
      g r s α P₀ hχs hχt Q Q'.1 Q'.2 hy]
  rw [Finset.sum_congr rfl (fun P _ => Finset.sum_congr rfl
    (fun Q' _ => hterm P Q'))]
  have hcollapse : ∀ P : CompIdx E r s,
      (∑ Q' : CompIdx E r s,
          covChartMetricGram (I := I) (M := M) g r s α P Q' y *
            (tensorComponentEuclid (I := I) (M := M) g r s F α P y *
              (chartPushedRaw I α
                  (rotatedSummandBump (I := I) (M := M) g r s α P₀ Q χ) y *
                (if (Q'.1, Q'.2) = Q then (1 : ℝ) else 0)))) =
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
          (tensorComponentEuclid (I := I) (M := M) g r s F α P y *
            chartPushedRaw I α
              (rotatedSummandBump (I := I) (M := M) g r s α P₀ Q χ) y) := by
    intro P
    rw [Finset.sum_eq_single Q]
    · rw [show ((Q.1, Q.2) : CompIdx E r s) = Q from Prod.ext rfl rfl,
        if_pos rfl, mul_one]
    · intro Q' _ hne
      rw [if_neg (fun h => hne (Prod.ext (congrArg Prod.fst h)
        (congrArg Prod.snd h))), _root_.MulZeroClass.mul_zero, _root_.MulZeroClass.mul_zero, _root_.MulZeroClass.mul_zero]
    · intro hQ
      exact absurd (Finset.mem_univ Q) hQ
  rw [Finset.sum_congr rfl (fun P _ => hcollapse P)]
  rw [chartPushedRaw_rotatedSummandBump_eq (I := I) (M := M) g r s α P₀ Q
    (χ := χ) hy]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorInnerPointwise_F_rotatedSummand_chart
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorInnerPointwise_F_rotatedSummand_chart target :: scope.openDecls } }

omit [CompleteSpace E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma tensorInnerPointwise_F_rotatedTestSection_chart
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorInnerPointwise (I := I) (M := M) g r s
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        (F.toFun ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        ((rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt).toFun
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) =
      chartPushedRaw I α χ y * sourcePairingCoeff (I := I) (M := M) g r s F α P₀
        y := by
  classical
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  rw [rotatedTestSection_toFun_apply (I := I) (M := M) g r s α P₀ hχs hχt b]
  have hadd :
      tensorInnerPointwise (I := I) (M := M) g r s b (F.toFun b)
          (∑ Q : CompIdx E r s,
            (rotatedSummand (I := I) (M := M) g r s α P₀ hχs hχt Q).toFun b) =
        ∑ Q : CompIdx E r s,
          tensorInnerPointwise (I := I) (M := M) g r s b (F.toFun b)
            ((rotatedSummand (I := I) (M := M) g r s α P₀ hχs hχt Q).toFun b) := by
    induction (Finset.univ : Finset (CompIdx E r s)) using Finset.induction with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        exact tensorInnerPointwise_zero_right (I := I) (M := M) g r s b
          (F.toFun b)
    | insert Q A hQ ih =>
        rw [Finset.sum_insert hQ, Finset.sum_insert hQ,
          tensorInnerPointwise_add_right, ih]
  rw [hadd]
  rw [Finset.sum_congr rfl (fun Q _ =>
    tensorInnerPointwise_F_rotatedSummand_chart (I := I) (M := M) g r s F α P₀
      hχs hχt Q hy)]
  rw [sourcePairingCoeff_def, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorInnerPointwise_F_rotatedTestSection_chart
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorInnerPointwise_F_rotatedTestSection_chart target :: scope.openDecls } }

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorL2Inner_rotatedTestSection_chart_pull
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source) :
    tensorL2Inner (I := I) (M := M) g r s F.toFun
        (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt).toFun =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y * chartPushedRaw I α χ y *
          sourcePairingCoeff (I := I) (M := M) g r s F α P₀ y
        ∂(MeasureTheory.Measure.map (toEuclidean : E → EuclN)
            (modelHaar (E := E))) := by
  classical
  rw [show tensorL2Inner (I := I) (M := M) g r s F.toFun
        (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt).toFun =
      ∫ x, tensorInnerPointwise (I := I) (M := M) g r s x (F.toFun x)
          ((rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt).toFun x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) from rfl]
  have hcont : Continuous
      (fun x : M =>
        tensorInnerPointwise (I := I) (M := M) g r s x (F.toFun x)
          ((rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt).toFun
            x)) :=
    sourcePairingIntegrand_continuous (I := I) (M := M) g r s F α P₀ hχs hχt
  have hsupp : tsupport
      (fun x : M =>
        tensorInnerPointwise (I := I) (M := M) g r s x (F.toFun x)
          ((rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt).toFun
            x)) ⊆
      (chartAt H α).source :=
    sourcePairingIntegrand_tsupport_subset (I := I) (M := M) g r s F α P₀ hχs
      hχt
  rw [integral_riemannianVolumeMeasure_eq_euclidean_chartTarget
    (I := I) (M := M) g α hcont hsupp]
  have hctE_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α).measurableSet
  refine _root_.MeasureTheory.setIntegral_congr_fun hctE_meas (fun y hy => ?_)
  rw [tensorInnerPointwise_F_rotatedTestSection_chart (I := I) (M := M)
    g r s F α P₀ hχs hχt hy]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorL2Inner_rotatedTestSection_chart_pull then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorL2Inner_rotatedTestSection_chart_pull"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorL2Inner_rotatedTestSection_chart_pull ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorL2Inner_rotatedTestSection_chart_pull

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry
