import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Calculus.SecondGradient
import Submission.DifferentialGeometry.Geometry.Metric.DeTurck.ConnectionDifference.Identities
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CovariantJetDecomposition.CorrectionFields.PointwiseBounds
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CovariantJetDecomposition.CoefficientFields
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.PalatiniDecomposition.PathLinearization
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.SectionDifference.ConnectionBicontraction
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Product.JetIntegral
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.Remainder.Defs
import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLie.Kernel.L2JetBound
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.Curvature.DecompositionMonomialBounds
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.ConnectionDifference.Coefficients
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Algebra.InputSlotSymmetrization

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Tensor.Multilinear
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator

noncomputable section
set_option backward.isDefEq.respectTransparency false

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2

open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.DeTurck
open _root_.Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

section NormedMetricPerturbation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instCompleteSpace_differentialGeometry_1 : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instCompleteSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instCompleteSpace_differentialGeometry_1 target :: scope.openDecls } }

def metricCcTensorFib (g : SmoothRiemannianMetric I M) (x : M) : Tensor0SSpace 2 I x :=
  (show ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I x) ℝ from
    { toFun := fun m => g.inner x (m 0) (m 1)
      map_update_add' := by
        have h01 : (0 : Fin 2) ≠ 1 := by decide
        have h10 : (1 : Fin 2) ≠ 0 := by decide
        intro _ m i a a'
        fin_cases i <;>
          simp only [Fin.reduceFinMk, Fin.isValue, Function.update_self, ne_eq,
            Function.update_of_ne, h01, h10, not_false_eq_true, map_add,
            add_apply]
      map_update_smul' := by
        have h01 : (0 : Fin 2) ≠ 1 := by decide
        have h10 : (1 : Fin 2) ≠ 0 := by decide
        intro _ m i c a
        fin_cases i <;>
          simp only [Fin.reduceFinMk, Fin.isValue, Function.update_self, ne_eq,
            Function.update_of_ne, h01, h10, not_false_eq_true, map_smul,
            smul_apply]
      cont := ((g.inner x).continuous.comp (continuous_apply 0)).clm_apply
        (continuous_apply 1) }
    : Tensor0SSpace 2 I x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensorFib then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensorFib"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensorFib ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensorFib

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma metricCcTensorFib_apply (g : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 2 → TangentSpace I x) :
    metricCcTensorFib (I := I) g x m = g.inner x (m 0) (m 1) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensorFib_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensorFib_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensorFib_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensorFib_apply

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem metricCcTensorFib_section_contMDiff (g : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x (metricCcTensorFib (I := I) g x)) := by
  classical
  let _ := Tensor0SBundle.tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x : M => (metricCcTensorFib (I := I) g x :
        Bundle.continuousMultilinearMap ℝ 2 E (TangentSpace I) x))).mpr ?_
  intro σ x₀
  set b := Module.finBasis ℝ E with hb
  set e₁ := _root_.FiberBundle.trivializationAt E (TangentSpace I : M → Type _) x₀ with he₁def
  have he₁ : x₀ ∈ e₁.baseSet := _root_.FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have hframe := e₁.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
  obtain ⟨Y, hY⟩ := hframe.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
  have hscalar : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g.inner x (Y (σ 0) x) (Y (σ 1) x)) x₀ :=
    (contMDiff_g_inner_of_smooth_sections (I := I) g (Y (σ 0)) (Y (σ 1))).contMDiffAt
  refine hscalar.congr_of_eventuallyEq ?_
  have h_base₁ : ∀ᶠ x in 𝓝 x₀, x ∈ e₁.baseSet := e₁.open_baseSet.mem_nhds he₁
  filter_upwards [h_base₁, hY] with x hx₁ hYx
  rw [continuousMultilinearMap_basis_repr]
  have hframeEq : ∀ k : Fin 2, e₁.symmL ℝ x (b (σ k)) = (Y (σ k)) x := by
    intro k
    rw [hYx (σ k), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
    exact e₁.symmL_apply hx₁ (b (σ k))
  change g.inner x (e₁.symmL ℝ x (b (σ 0))) (e₁.symmL ℝ x (b (σ 1))) = _
  rw [hframeEq 0, hframeEq 1]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensorFib_section_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensorFib_section_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensorFib_section_contMDiff ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensorFib_section_contMDiff

def metricCcTensor (g₀ g : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 2 where
  toSection :=
    MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞
      (letI := Tensor0SBundle.tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I)
        (M := M) 2
       (⟨fun x => metricCcTensorFib (I := I) g x,
         metricCcTensorFib_section_contMDiff (I := I) g⟩ :
        Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 2))
  hasCompactSupport := HasCompactSupport.of_compactSpace _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensor ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensor

def metricDifferenceCcTensor (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 2 :=
  metricCcTensor (I := I) (M := M) g₀ g₁ - metricCcTensor (I := I) (M := M) g₀ g₀

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor

omit [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem metricDifferenceCcTensor_self (g₀ : SmoothRiemannianMetric I M) :
    metricDifferenceCcTensor (I := I) (M := M) g₀ g₀ = 0 :=
  sub_self _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor_self ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor_self

def ccTensorUnitValueSection (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    Π y : M, Tensor0SSpace 2 I y :=
  fun y =>
    (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 2 I y from T.toSection y)
      (unitZeroSec (I := I) (M := M) y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ccTensorUnitValueSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ccTensorUnitValueSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ccTensorUnitValueSection ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ccTensorUnitValueSection

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem ccTensorUnitValueSection_contMDiff (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) y
        (ccTensorUnitValueSection (I := I) (M := M) g T y)) := by
  exact ContMDiff.clm_bundle_apply (𝕜 := ℝ) (n := (∞ : WithTop ℕ∞))
    (F₁ := Tensor0SModel 0 ℝ E) (F₂ := Tensor0SModel 2 ℝ E)
    (E₁ := fun z : M => Tensor0SSpace 0 I z)
    (E₂ := fun z : M => Tensor0SSpace 2 I z)
    (IM := I) (IB := I) (b := id)
    (ϕ := fun y : M =>
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 2 I y from T.toSection y))
    (v := fun y : M => unitZeroSec (I := I) (M := M) y)
    T.toSection.contMDiff (unitZeroSec (I := I) (M := M)).contMDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ccTensorUnitValueSection_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ccTensorUnitValueSection_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ccTensorUnitValueSection_contMDiff ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ccTensorUnitValueSection_contMDiff

omit [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem metricCcTensor_ccTensorBilin (g₀ g : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    smoothCcTensorBilinForm (I := I) g₀ (metricCcTensor (I := I) (M := M) g₀ g) x v w =
      g.inner x v w := by
  let _ := Tensor0SBundle.tensor0SBundleTopology
    (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  have hround : ccTensorMultilinear (I := I) g₀ (metricCcTensor (I := I) (M := M) g₀ g) x =
      metricCcTensorFib (I := I) g x := by
    unfold ccTensorMultilinear metricCcTensor
    unfold MixedSection.toMultilinearSection MixedSection.fromMultilinearSection
    change
      (MixedSection.eval₀ (𝕜 := ℝ) (F := E)
        (E := (TangentSpace I : M → Type _)) x).smulRight
          (metricCcTensorFib (I := I) g x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) 1) =
        metricCcTensorFib (I := I) g x
    rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
      ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rw [ccTensorBilin_apply]
  unfold ccTensorModel
  rw [hround]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensor_ccTensorBilin
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensor_ccTensorBilin target :: scope.openDecls } }

end NormedMetricPerturbation

def gInvDiffQuadResidualField (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 :=
  connectionDifferenceBiContrCoeffField (I := I) (M := M) g₁ g₀ g₁ g₀

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.gInvDiffQuadResidualField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.gInvDiffQuadResidualField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.gInvDiffQuadResidualField ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.gInvDiffQuadResidualField

omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
@[simp] theorem gInvDiffQuadResidualField_toSection (g₀ g₁ : SmoothRiemannianMetric I M)
    (x : M) :
    (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁).toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (connectionDifferenceBiContrFib (I := I) g₁ g₀ g₁ g₀ x)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.gInvDiffQuadResidualField_toSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.gInvDiffQuadResidualField_toSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.gInvDiffQuadResidualField_toSection ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.gInvDiffQuadResidualField_toSection

omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem gInvDiffQuadResidualField_self (g₀ : SmoothRiemannianMetric I M) :
    gInvDiffQuadResidualField (I := I) (M := M) g₀ g₀ = 0 := by
  classical
  refine SmoothCcTensor.ext ?_
  refine ContMDiffSection.ext (fun x => ?_)
  rw [gInvDiffQuadResidualField_toSection]
  have hzero : connectionDifferenceBiContrFib (I := I) g₀ g₀ g₀ g₀ x = 0 := by
    apply ContinuousLinearMap.ext
    intro D
    apply Tensor0SSpace.toModel_injective
    apply ContinuousMultilinearMap.ext
    intro v
    rw [show connectionDifferenceBiContrFib (I := I) g₀ g₀ g₀ g₀ x =
        connectionDifferenceBiContrFibFixedFrame (I := I) g₀ g₀ g₀ g₀
          (smoothOrthoFrame (I := I) g₀ x) x from rfl]
    rw [connectionDifferenceBiContrFibFixedFrame_toModel]
    have hconn : PDE.DeTurck.connectionDifference (I := I) g₀ g₀ = 0 :=
      PDE.DeTurck.connectionDifference_self (I := I) g₀
    simp only [hconn, Pi.zero_apply, zero_apply, map_zero,
      _root_.MulZeroClass.zero_mul, Finset.sum_const_zero, Tensor0SSpace.toModel_zero]
  rw [hzero]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.gInvDiffQuadResidualField_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.gInvDiffQuadResidualField_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.gInvDiffQuadResidualField_self ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.gInvDiffQuadResidualField_self

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
