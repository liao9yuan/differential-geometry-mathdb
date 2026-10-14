import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.GradInner.Laplacian.Rhs.Pairings
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Ricci.DualNorm
import Mathlib.Analysis.Normed.Operator.Extend

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter _root_.Topology _root_.Function
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix _root_.InnerProductSpace _root_.BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace RicciPairingCLM

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem

open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLpIdentity
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

noncomputable def ricciPairingSmooth
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  smoothRicciPairingLp (I := I) (M := M) g φ v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmooth ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmooth

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma ricciPairingSmooth_def
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) :
    ricciPairingSmooth (I := I) (M := M) g φ v =
      smoothRicciPairingLp (I := I) (M := M) g φ v := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmooth_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmooth_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmooth_def ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmooth_def

omit [NeZero (Module.finrank ℝ E)] in
lemma ricciPairingSmooth_coeFn
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) :
    (ricciPairingSmooth (I := I) (M := M) g φ v :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (fun b : M =>
        ricciTensor (I := I) g b
          (gradFun (I := I) g φ b) (gradFun (I := I) g v.toFun b)) :=
  smoothRicciPairingLp_coeFn (I := I) (M := M) g φ v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmooth_coeFn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmooth_coeFn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmooth_coeFn ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmooth_coeFn

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma ricciPairingSmooth_pt_add
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (v w : SmoothScalar g) (b : M) :
    ricciTensor (I := I) g b (gradFun (I := I) g φ b)
        (gradFun (I := I) g (v + w).toFun b) =
      ricciTensor (I := I) g b (gradFun (I := I) g φ b)
          (gradFun (I := I) g v.toFun b) +
        ricciTensor (I := I) g b (gradFun (I := I) g φ b)
          (gradFun (I := I) g w.toFun b) := by
  have hgrad_add : gradFun (I := I) g (v + w).toFun b =
      gradFun (I := I) g v.toFun b + gradFun (I := I) g w.toFun b := by
    have hfun : (v + w).toFun = v.toFun + w.toFun := rfl
    rw [hfun]
    exact DifferentialGeometry.Geometry.Operator.gradFun_add (I := I) g
      (v.smooth.mdifferentiable (by simp) b)
      (w.smooth.mdifferentiable (by simp) b)
  rw [hgrad_add, ContinuousLinearMap.map_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmooth_pt_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmooth_pt_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmooth_pt_add ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmooth_pt_add

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma ricciPairingSmooth_pt_smul
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (c : ℝ) (v : SmoothScalar g) (b : M) :
    ricciTensor (I := I) g b (gradFun (I := I) g φ b)
        (gradFun (I := I) g (c • v).toFun b) =
      c * ricciTensor (I := I) g b (gradFun (I := I) g φ b)
        (gradFun (I := I) g v.toFun b) := by
  have hgrad_smul : gradFun (I := I) g (c • v).toFun b =
      c • gradFun (I := I) g v.toFun b := by
    have h := SmoothScalar.grad_g_smul_apply (I := I) (g := g) c v b
    change gradFun (I := I) g (c • v).toFun b =
      c • gradFun (I := I) g v.toFun b at h
    exact h
  rw [hgrad_smul]
  rw [ContinuousLinearMap.map_smul, smul_eq_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmooth_pt_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmooth_pt_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmooth_pt_smul ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmooth_pt_smul

omit [NeZero (Module.finrank ℝ E)] in
theorem ricciPairingSmooth_add
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (v w : SmoothScalar g) :
    ricciPairingSmooth (I := I) (M := M) g φ (v + w) =
      ricciPairingSmooth (I := I) (M := M) g φ v +
        ricciPairingSmooth (I := I) (M := M) g φ w := by
  apply MeasureTheory.Lp.ext
  have h_sum_coe := MeasureTheory.Lp.coeFn_add
    (ricciPairingSmooth (I := I) (M := M) g φ v)
    (ricciPairingSmooth (I := I) (M := M) g φ w)
  have h_lhs := ricciPairingSmooth_coeFn (I := I) (M := M) g φ (v + w)
  have h_v := ricciPairingSmooth_coeFn (I := I) (M := M) g φ v
  have h_w := ricciPairingSmooth_coeFn (I := I) (M := M) g φ w
  refine h_lhs.trans ?_
  refine EventuallyEq.symm ?_
  filter_upwards [h_sum_coe, h_v, h_w] with b h_sum h_v_eq h_w_eq
  rw [h_sum, Pi.add_apply, h_v_eq, h_w_eq]
  exact (ricciPairingSmooth_pt_add (I := I) (M := M) g φ v w b).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmooth_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmooth_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmooth_add ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmooth_add

omit [NeZero (Module.finrank ℝ E)] in
theorem ricciPairingSmooth_smul
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (c : ℝ) (v : SmoothScalar g) :
    ricciPairingSmooth (I := I) (M := M) g φ (c • v) =
      c • ricciPairingSmooth (I := I) (M := M) g φ v := by
  apply MeasureTheory.Lp.ext
  have h_smul_coe := MeasureTheory.Lp.coeFn_smul c
    (ricciPairingSmooth (I := I) (M := M) g φ v)
  have h_lhs := ricciPairingSmooth_coeFn (I := I) (M := M) g φ (c • v)
  have h_v := ricciPairingSmooth_coeFn (I := I) (M := M) g φ v
  refine h_lhs.trans ?_
  refine EventuallyEq.symm ?_
  filter_upwards [h_smul_coe, h_v] with b h_smul h_v_eq
  rw [h_smul, Pi.smul_apply, h_v_eq, smul_eq_mul]
  exact (ricciPairingSmooth_pt_smul (I := I) (M := M) g φ c v b).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmooth_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmooth_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmooth_smul ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmooth_smul

noncomputable def ricciPairingSmoothLin
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) :
    SmoothScalar g →ₗ[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) where
  toFun v := ricciPairingSmooth (I := I) (M := M) g φ v
  map_add' v w := ricciPairingSmooth_add (I := I) (M := M) g φ v w
  map_smul' c v := ricciPairingSmooth_smul (I := I) (M := M) g φ c v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmoothLin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmoothLin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmoothLin ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmoothLin

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma ricciPairingSmoothLin_apply
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) :
    ricciPairingSmoothLin (I := I) (M := M) g φ v =
      ricciPairingSmooth (I := I) (M := M) g φ v := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmoothLin_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmoothLin_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmoothLin_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmoothLin_apply

noncomputable def ricciPairingCLMOnSmoothOfBound
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (C : ℝ)
    (hC_bound : ∀ v : SmoothScalar g,
      ‖ricciPairingSmooth (I := I) (M := M) g φ v‖ ≤ C * ‖v‖) :
    SmoothScalar g →L[ℝ] _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  (ricciPairingSmoothLin (I := I) (M := M) g φ).mkContinuous C hC_bound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingCLMOnSmoothOfBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingCLMOnSmoothOfBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingCLMOnSmoothOfBound ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingCLMOnSmoothOfBound

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma ricciPairingCLMOnSmoothOfBound_apply
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (C : ℝ)
    (hC_bound : ∀ v : SmoothScalar g,
      ‖ricciPairingSmooth (I := I) (M := M) g φ v‖ ≤ C * ‖v‖)
    (v : SmoothScalar g) :
    ricciPairingCLMOnSmoothOfBound (I := I) (M := M) g φ C hC_bound v =
      ricciPairingSmooth (I := I) (M := M) g φ v := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingCLMOnSmoothOfBound_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingCLMOnSmoothOfBound_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingCLMOnSmoothOfBound_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingCLMOnSmoothOfBound_apply

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma denseRange_toComplL_smoothScalar
    (g : SmoothRiemannianMetric I M) :
    DenseRange (UniformSpace.Completion.toComplL :
      SmoothScalar g →L[ℝ] H1Compl g) := by
  rw [show (UniformSpace.Completion.toComplL : SmoothScalar g → H1Compl g) =
      ((↑) : SmoothScalar g → UniformSpace.Completion (SmoothScalar g)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.denseRange_coe

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.denseRange_toComplL_smoothScalar
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.denseRange_toComplL_smoothScalar target :: scope.openDecls } }

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma isUniformInducing_toComplL_smoothScalar
    (g : SmoothRiemannianMetric I M) :
    IsUniformInducing
      (UniformSpace.Completion.toComplL :
        SmoothScalar g →L[ℝ] H1Compl g) := by
  rw [show (UniformSpace.Completion.toComplL : SmoothScalar g → H1Compl g) =
      ((↑) : SmoothScalar g → UniformSpace.Completion (SmoothScalar g)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.isUniformInducing_coe (SmoothScalar g)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.isUniformInducing_toComplL_smoothScalar
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.isUniformInducing_toComplL_smoothScalar target :: scope.openDecls } }

noncomputable def ricciPairingCLMOfBound
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (C : ℝ)
    (hC_bound : ∀ v : SmoothScalar g,
      ‖ricciPairingSmooth (I := I) (M := M) g φ v‖ ≤ C * ‖v‖) :
    H1Compl g →L[ℝ] _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  ContinuousLinearMap.extend
    (ricciPairingCLMOnSmoothOfBound (I := I) (M := M) g φ C hC_bound)
    (UniformSpace.Completion.toComplL :
      SmoothScalar g →L[ℝ] H1Compl g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingCLMOfBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingCLMOfBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingCLMOfBound ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingCLMOfBound

omit [NeZero (Module.finrank ℝ E)] in
theorem ricciPairingCLMOfBound_smoothToH1Compl
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (C : ℝ)
    (hC_bound : ∀ v : SmoothScalar g,
      ‖ricciPairingSmooth (I := I) (M := M) g φ v‖ ≤ C * ‖v‖)
    (v : SmoothScalar g) :
    ricciPairingCLMOfBound (I := I) (M := M) g φ C hC_bound
        (smoothToH1Compl (I := I) (M := M) g v) =
      ricciPairingSmooth (I := I) (M := M) g φ v := by
  unfold ricciPairingCLMOfBound
  exact ContinuousLinearMap.extend_eq
    (ricciPairingCLMOnSmoothOfBound (I := I) (M := M) g φ C hC_bound)
    (e := UniformSpace.Completion.toComplL)
    (denseRange_toComplL_smoothScalar (I := I) (M := M) g)
    (isUniformInducing_toComplL_smoothScalar (I := I) (M := M) g) v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingCLMOfBound_smoothToH1Compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingCLMOfBound_smoothToH1Compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingCLMOfBound_smoothToH1Compl ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingCLMOfBound_smoothToH1Compl

omit [NeZero (Module.finrank ℝ E)] in
lemma ricciPairingSmooth_norm_nonneg
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    0 ≤ ‖ricciPairingSmooth (I := I) (M := M) g φ v‖ :=
  norm_nonneg _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmooth_norm_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmooth_norm_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmooth_norm_nonneg ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmooth_norm_nonneg

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
lemma smoothRicciPairing_continuous
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) :
    Continuous (fun b : M => ricciTensor (I := I) g b
      (gradFun (I := I) g φ b) (gradFun (I := I) g v.toFun b)) :=
  (smoothRicciPairing_contMDiff (I := I) (M := M) g φ v).continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.smoothRicciPairing_continuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.smoothRicciPairing_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.smoothRicciPairing_continuous ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.smoothRicciPairing_continuous

open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.RicciDualNorm

omit [NeZero (Module.finrank ℝ E)] in
lemma ricciPairingSmooth_norm_sq
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    ‖ricciPairingSmooth (I := I) (M := M) g φ v‖ ^ 2 =
      ∫ b, (ricciTensor (I := I) g b
              (gradFun (I := I) g φ b) (gradFun (I := I) g v.toFun b)) ^ 2
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  have h := real_inner_self_eq_norm_sq
    (ricciPairingSmooth (I := I) (M := M) g φ v)
  rw [L2.inner_def (𝕜 := ℝ)] at h
  have hae_coe := ricciPairingSmooth_coeFn (I := I) (M := M) g φ v
  have hae : (fun a : M =>
        @_root_.Inner.inner ℝ _ _
          ((ricciPairingSmooth (I := I) (M := M) g φ v :
              _root_.MeasureTheory.Lp ℝ 2 _) a)
          ((ricciPairingSmooth (I := I) (M := M) g φ v :
              _root_.MeasureTheory.Lp ℝ 2 _) a)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (fun a : M =>
        (ricciTensor (I := I) g a
          (gradFun (I := I) g φ a) (gradFun (I := I) g v.toFun a)) ^ 2) := by
    filter_upwards [hae_coe] with a hae_a
    rw [hae_a]
    rw [show (ricciTensor (I := I) g a (gradFun (I := I) g φ a)
            (gradFun (I := I) g v.toFun a)) ^ 2 =
        (ricciTensor (I := I) g a (gradFun (I := I) g φ a)
            (gradFun (I := I) g v.toFun a)) *
        (ricciTensor (I := I) g a (gradFun (I := I) g φ a)
            (gradFun (I := I) g v.toFun a)) from sq _]
    rfl
  rw [_root_.MeasureTheory.integral_congr_ae hae] at h
  exact h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmooth_norm_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmooth_norm_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmooth_norm_sq ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmooth_norm_sq

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma ricciPairing_sq_le_C_mul_grad
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {C : ℝ} (hC_bound : ∀ b : M,
      g.inner b (ricciSharp (I := I) g φ b) (ricciSharp (I := I) g φ b) ≤ C)
    (v : SmoothScalar g) (b : M) :
    (ricciTensor (I := I) g b
        (gradFun (I := I) g φ b) (gradFun (I := I) g v.toFun b)) ^ 2 ≤
      C * g.inner b (gradFun (I := I) g v.toFun b) (gradFun (I := I) g v.toFun b) := by
  have h_cs := ricciPairing_cs_sq (I := I) g φ b (gradFun (I := I) g v.toFun b)
  have h_grad_nn : 0 ≤ g.inner b (gradFun (I := I) g v.toFun b)
      (gradFun (I := I) g v.toFun b) :=
    metric_inner_self_nonneg (I := I) (M := M) g b _
  calc (ricciTensor (I := I) g b
          (gradFun (I := I) g φ b) (gradFun (I := I) g v.toFun b)) ^ 2
      ≤ g.inner b (ricciSharp (I := I) g φ b)
            (ricciSharp (I := I) g φ b) *
          g.inner b (gradFun (I := I) g v.toFun b)
            (gradFun (I := I) g v.toFun b) := h_cs
    _ ≤ C * g.inner b (gradFun (I := I) g v.toFun b)
            (gradFun (I := I) g v.toFun b) :=
        mul_le_mul_of_nonneg_right (hC_bound b) h_grad_nn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairing_sq_le_C_mul_grad then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairing_sq_le_C_mul_grad"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairing_sq_le_C_mul_grad ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairing_sq_le_C_mul_grad

omit [NeZero (Module.finrank ℝ E)] in
lemma ricciPairingSmooth_norm_sq_le
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {C : ℝ} (hC_nn : 0 ≤ C) (hC_bound : ∀ b : M,
      g.inner b (ricciSharp (I := I) g φ b) (ricciSharp (I := I) g φ b) ≤ C)
    (v : SmoothScalar g) :
    ‖ricciPairingSmooth (I := I) (M := M) g φ v‖ ^ 2 ≤ C * ‖v‖ ^ 2 := by
  rw [ricciPairingSmooth_norm_sq (I := I) (M := M) g φ v]
  have h_pt : ∀ b : M,
      (ricciTensor (I := I) g b (gradFun (I := I) g φ b)
          (gradFun (I := I) g v.toFun b)) ^ 2 ≤
        C * g.inner b (gradFun (I := I) g v.toFun b)
            (gradFun (I := I) g v.toFun b) := fun b =>
    ricciPairing_sq_le_C_mul_grad (I := I) (M := M) g φ hC_bound v b
  have : _root_.MeasureTheory.IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  have hLHS_cont : Continuous (fun b : M =>
      (ricciTensor (I := I) g b (gradFun (I := I) g φ b)
          (gradFun (I := I) g v.toFun b)) ^ 2) :=
    (smoothRicciPairing_continuous (I := I) (M := M) g φ v).pow 2
  have hLHS_int : _root_.MeasureTheory.Integrable (fun b : M =>
      (ricciTensor (I := I) g b (gradFun (I := I) g φ b)
          (gradFun (I := I) g v.toFun b)) ^ 2)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    hLHS_cont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hgrad_cont : Continuous (fun b : M =>
      g.inner b (gradFun (I := I) g v.toFun b) (gradFun (I := I) g v.toFun b)) := by
    exact gradInnerSmooth_continuous (I := I) (M := M) g
      ⟨v.toFun, v.smooth⟩ v
  have hgrad_int : _root_.MeasureTheory.Integrable (fun b : M =>
      g.inner b (gradFun (I := I) g v.toFun b) (gradFun (I := I) g v.toFun b))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    hgrad_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hRHS_int : _root_.MeasureTheory.Integrable (fun b : M =>
      C * g.inner b (gradFun (I := I) g v.toFun b)
          (gradFun (I := I) g v.toFun b))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    hgrad_int.const_mul _
  have h_int_le := _root_.MeasureTheory.integral_mono_ae hLHS_int hRHS_int
    (Filter.Eventually.of_forall h_pt)
  rw [_root_.MeasureTheory.integral_const_mul] at h_int_le
  have h_grad_int_le := integral_inner_grad_self_le_h1_norm_sq (g := g) v
  exact le_trans h_int_le (mul_le_mul_of_nonneg_left h_grad_int_le hC_nn)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmooth_norm_sq_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmooth_norm_sq_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmooth_norm_sq_le ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmooth_norm_sq_le

omit [NeZero (Module.finrank ℝ E)] in
lemma ricciPairingSmooth_norm_le
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {C : ℝ} (hC_nn : 0 ≤ C) (hC_bound : ∀ b : M,
      g.inner b (ricciSharp (I := I) g φ b) (ricciSharp (I := I) g φ b) ≤ C)
    (v : SmoothScalar g) :
    ‖ricciPairingSmooth (I := I) (M := M) g φ v‖ ≤ Real.sqrt C * ‖v‖ := by
  have h_sq : ‖ricciPairingSmooth (I := I) (M := M) g φ v‖ ^ 2 ≤
      (Real.sqrt C * ‖v‖) ^ 2 := by
    have h := ricciPairingSmooth_norm_sq_le (I := I) (M := M) g φ hC_nn hC_bound v
    have hrhs : (Real.sqrt C * ‖v‖) ^ 2 = C * ‖v‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hC_nn]
    rw [hrhs]
    exact h
  have h_lhs_nn : 0 ≤ ‖ricciPairingSmooth (I := I) (M := M) g φ v‖ :=
    norm_nonneg _
  have h_rhs_nn : 0 ≤ Real.sqrt C * ‖v‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  exact abs_le_of_sq_le_sq' h_sq h_rhs_nn |>.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmooth_norm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmooth_norm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmooth_norm_le ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingSmooth_norm_le

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_ricciPairing_lipschitz_bound
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : SmoothScalar g,
      ‖ricciPairingSmooth (I := I) (M := M) g φ v‖ ≤ C * ‖v‖ := by
  obtain ⟨C_sq, hC_sq_nn, hC_bound⟩ :=
    exists_global_ricci_dual_normSq_bound (I := I) (M := M) g φ
  refine ⟨Real.sqrt C_sq, Real.sqrt_nonneg _, ?_⟩
  intro v
  exact ricciPairingSmooth_norm_le (I := I) (M := M) g φ hC_sq_nn hC_bound v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.exists_ricciPairing_lipschitz_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.exists_ricciPairing_lipschitz_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.exists_ricciPairing_lipschitz_bound ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.exists_ricciPairing_lipschitz_bound

noncomputable def ricciPairingCLMOnSmooth
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) :
    SmoothScalar g →L[ℝ] _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  ricciPairingCLMOnSmoothOfBound (I := I) (M := M) g φ
    (Classical.choose (exists_ricciPairing_lipschitz_bound (I := I) (M := M) g φ))
    (Classical.choose_spec
      (exists_ricciPairing_lipschitz_bound (I := I) (M := M) g φ)).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingCLMOnSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingCLMOnSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingCLMOnSmooth ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingCLMOnSmooth

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma ricciPairingCLMOnSmooth_apply
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) :
    ricciPairingCLMOnSmooth (I := I) (M := M) g φ v =
      ricciPairingSmooth (I := I) (M := M) g φ v := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingCLMOnSmooth_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingCLMOnSmooth_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingCLMOnSmooth_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingCLMOnSmooth_apply

noncomputable def ricciPairingCLM
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) :
    H1Compl g →L[ℝ] _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  ricciPairingCLMOfBound (I := I) (M := M) g φ
    (Classical.choose (exists_ricciPairing_lipschitz_bound (I := I) (M := M) g φ))
    (Classical.choose_spec
      (exists_ricciPairing_lipschitz_bound (I := I) (M := M) g φ)).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingCLM ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingCLM

omit [NeZero (Module.finrank ℝ E)] in
theorem ricciPairingCLM_smoothToH1Compl
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    ricciPairingCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) =
      ricciPairingSmooth (I := I) (M := M) g φ v := by
  unfold ricciPairingCLM
  exact ricciPairingCLMOfBound_smoothToH1Compl (I := I) (M := M) g φ _ _ v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingCLM_smoothToH1Compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingCLM_smoothToH1Compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingCLM_smoothToH1Compl ``Submission.DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM.ricciPairingCLM_smoothToH1Compl

end RicciPairingCLM
end Laplacian
end Analysis
end DifferentialGeometry

end
