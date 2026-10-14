import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CovariantJetDecomposition.OperatorField.Application
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CovariantJetDecomposition.CorrectionFields.ChristoffelCoefficients
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Parametric.JointSmoothness
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Identities.ContractedBianchi
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.SlotSubstitutionBound
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CovariantJetDecomposition.DeTurckLie.SecondOrderTraceCoefficient
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifference.LoweredTrilinear

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Connection.Realization _root_.Submission.DifferentialGeometry.Tensor.Multilinear
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators _root_.Matrix _root_.Submission.Matrix

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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

def deTurckLieFirstOrderPairPermCorrection : Equiv.Perm (Fin 6) :=
  ⟨![4, 0, 2, 1, 3, 5], ![1, 3, 2, 4, 0, 5], by decide, by decide⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderPairPermCorrection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderPairPermCorrection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderPairPermCorrection ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderPairPermCorrection

def deTurckLieFirstOrderPairPermOuterZero : Equiv.Perm (Fin 6) :=
  ⟨![0, 5, 2, 4, 3, 1], ![0, 5, 2, 4, 3, 1], by decide, by decide⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderPairPermOuterZero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderPairPermOuterZero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderPairPermOuterZero ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderPairPermOuterZero

def deTurckLieFirstOrderPairPermOuterTwo : Equiv.Perm (Fin 6) :=
  ⟨![0, 5, 2, 4, 1, 3], ![0, 4, 2, 5, 3, 1], by decide, by decide⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderPairPermOuterTwo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderPairPermOuterTwo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderPairPermOuterTwo ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderPairPermOuterTwo

def deTurckLieFirstOrderPairPermInnerTwo : Equiv.Perm (Fin 6) :=
  ⟨![4, 0, 2, 5, 1, 3], ![1, 4, 2, 5, 0, 3], by decide, by decide⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderPairPermInnerTwo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderPairPermInnerTwo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderPairPermInnerTwo ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderPairPermInnerTwo

def deTurckLieFirstOrderVecSlotPerm : Equiv.Perm (Fin 3) :=
  ⟨![1, 2, 0], ![2, 0, 1], by decide, by decide⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderVecSlotPerm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderVecSlotPerm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderVecSlotPerm ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderVecSlotPerm

def deTurckLieFirstOrderKoszulMidPerm : Equiv.Perm (Fin 3) :=
  ⟨![0, 2, 1], ![0, 2, 1], by decide, by decide⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderKoszulMidPerm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderKoszulMidPerm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderKoszulMidPerm ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderKoszulMidPerm

def deTurckLieFirstOrderKoszulZeroPerm : Equiv.Perm (Fin 3) :=
  ⟨![2, 0, 1], ![1, 2, 0], by decide, by decide⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderKoszulZeroPerm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderKoszulZeroPerm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderKoszulZeroPerm ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderKoszulZeroPerm

noncomputable def deTurckLiePairTraceFib (g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 6)) (x : M) (κ : Tensor0SBundle.Tensor0SSpace 3 I x) :
    Tensor0SBundle.Tensor0SSpace 3 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  ((cometricDoubleTraceFib (I := I) g₁ 2 x).comp
      ((cometricDoubleTraceFib (I := I) g₁ 4 x).comp
        (domDomCongrFibRank (I := I) 6 σ x))).comp
    (tensor0SProdKappaFib (I := I) (p := 3) (q := 3) x κ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLiePairTraceFib then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLiePairTraceFib"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLiePairTraceFib ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLiePairTraceFib

noncomputable def deTurckLieKoszulTraceFib (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 3)) (x : M) :
    Tensor0SBundle.Tensor0SSpace 3 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  (show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
      connectionDifferenceFib (I := I) g₁ g₀ x).comp
    ((cometricDoubleTraceFib (I := I) g₁ 1 x).comp
      (domDomCongrFibRank (I := I) 3 σ x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieKoszulTraceFib then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieKoszulTraceFib"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieKoszulTraceFib ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieKoszulTraceFib

noncomputable def deTurckLieFirstOrderCoreFib (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.Tensor0SSpace 3 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  deTurckLiePairTraceFib (I := I) g₁ deTurckLieFirstOrderPairPermInnerTwo x
      (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ x)
    - deTurckLiePairTraceFib (I := I) g₁ deTurckLieFirstOrderPairPermCorrection x
        (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g_bg x)
    - (Tensor0SBundle.interiorProduct (𝕜 := ℝ) (I := I) 2 x
          ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x)).comp
        (domDomCongrFibRank (I := I) 3 deTurckLieFirstOrderVecSlotPerm x)
    - deTurckLiePairTraceFib (I := I) g₁ deTurckLieFirstOrderPairPermOuterZero x
        (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ x)
    - deTurckLieKoszulTraceFib (I := I) g₀ g₁ deTurckLieFirstOrderKoszulMidPerm x
    - deTurckLiePairTraceFib (I := I) g₁ deTurckLieFirstOrderPairPermOuterTwo x
        (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderCoreFib then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderCoreFib"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderCoreFib ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderCoreFib

noncomputable def deTurckLieFirstOrderFib (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.Tensor0SSpace 3 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  Tensor0SBundle.interiorProduct (𝕜 := ℝ) (I := I) 2 x
      ((PDE.DeTurck.deTurckVF (I := I) g₁ g_bg : Π b : M, TangentSpace I b) x)
    + deTurckLieFirstOrderCoreFib (I := I) g₀ g₁ g_bg x
    + (domDomCongrFibRank (I := I) 2 (Equiv.swap (0 : Fin 2) 1) x).comp
        (deTurckLieFirstOrderCoreFib (I := I) g₀ g₁ g_bg x)
    + deTurckLieKoszulTraceFib (I := I) g₀ g₁ deTurckLieFirstOrderKoszulZeroPerm x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderFib then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderFib"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderFib ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderFib

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
private theorem tensor0SProd_section_contMDiff {p q : ℕ}
    (Y : ∀ x : M, Tensor0SBundle.Tensor0SSpace p I x)
    (K : ∀ x : M, Tensor0SBundle.Tensor0SSpace q I x)
    (hY : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel p ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel p ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace p I z) x (Y x)))
    (hK : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel q ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel q ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace q I z) x (K x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (p + q) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (p + q) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (p + q) I z) x
        (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
            (Tensor0SBundle.Tensor0SSpace.toModel (Y x))
            (Tensor0SBundle.Tensor0SSpace.toModel (K x))))) := by
  classical
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
          (Tensor0SBundle.Tensor0SSpace.toModel (Y x))
          (Tensor0SBundle.Tensor0SSpace.toModel (K x))) :
          Tensor0SBundle.Tensor0SSpace (p + q) I x))).mpr ?_
  have hYc := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => Y x)).mp hY
  have hKc := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => K x)).mp hK
  intro τ x₀
  refine (((contMDiffAt_const (I := I) (x := x₀) (n := (∞ : WithTop ℕ∞))
    (c := ContinuousLinearMap.mul ℝ ℝ)).clm_apply
      (hYc (τ ∘ Fin.castAdd q) x₀)).clm_apply
        (hKc (τ ∘ Fin.natAdd p) x₀)).congr_of_eventuallyEq ?_
  filter_upwards [Filter.univ_mem] with x _
  rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr,
    continuousMultilinearMap_basis_repr]
  set symmL := (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL ℝ x with hsymmL
  change (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
      (Tensor0SBundle.Tensor0SSpace.toModel (Y x)) (Tensor0SBundle.Tensor0SSpace.toModel (K x)))
      (fun j => tangentSpaceModelContinuousLinearEquiv (I := I) x
        (symmL ((Module.finBasis ℝ E) (τ j)))) = _
  rw [Bundle.continuousMultilinearMap.modelProduct_apply]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensor0SProd_section_contMDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensor0SProd_section_contMDiff target :: scope.openDecls } }


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem deTurckLiePairTraceFib_apply_section_contMDiff
    (g₁ : SmoothRiemannianMetric I M) (σ : Equiv.Perm (Fin 6))
    (κ : ∀ x : M, Tensor0SBundle.Tensor0SSpace 3 I x)
    (hκ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) x (κ x)))
    (Y : ContMDiffSection I (Tensor0SBundle.Tensor0SModel 3 ℝ E) ∞
      (fun x : M => Tensor0SBundle.Tensor0SSpace 3 I x)) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x
        (deTurckLiePairTraceFib (I := I) g₁ σ x (κ x) (Y x))) := by
  classical
  have hprod := tensor0SProd_section_contMDiff (I := I) (p := 3) (q := 3)
    (fun x => Y x) κ Y.contMDiff hκ
  have hperm := domDomCongr_section_contMDiff_local (I := I) (d := 6) σ
    (fun x => Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
      (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) 3 3
        (Tensor0SBundle.Tensor0SSpace.toModel (Y x))
        (Tensor0SBundle.Tensor0SSpace.toModel (κ x)))) hprod
  have htr4 := ContMDiff.clm_bundle_apply (b := id)
    (cometricDoubleTraceFib_contMDiff (I := I) g₁ 4) hperm
  have htr2 := ContMDiff.clm_bundle_apply (b := id)
    (cometricDoubleTraceFib_contMDiff (I := I) g₁ 2) htr4
  refine htr2.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x t) ?_
  rw [deTurckLiePairTraceFib, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, tensor0SProdKappaFib_apply, domDomCongrFibRank_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLiePairTraceFib_apply_section_contMDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLiePairTraceFib_apply_section_contMDiff target :: scope.openDecls } }


omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem deTurckLieKoszulTraceFib_apply_section_contMDiff
    (g₀ g₁ : SmoothRiemannianMetric I M) (σ : Equiv.Perm (Fin 3))
    (Y : ContMDiffSection I (Tensor0SBundle.Tensor0SModel 3 ℝ E) ∞
      (fun x : M => Tensor0SBundle.Tensor0SSpace 3 I x)) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x
        (deTurckLieKoszulTraceFib (I := I) g₀ g₁ σ x (Y x))) := by
  classical
  have hperm := domDomCongr_section_contMDiff_local (I := I) (d := 3) σ
    (fun x => Y x) Y.contMDiff
  have htr1 := ContMDiff.clm_bundle_apply (b := id)
    (cometricDoubleTraceFib_contMDiff (I := I) g₁ 1) hperm
  have hkos := ContMDiff.clm_bundle_apply (b := id)
    (connectionDifferenceFib_contMDiff (I := I) g₁ g₀) htr1
  refine hkos.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x t) ?_
  rw [deTurckLieKoszulTraceFib, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    domDomCongrFibRank_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieKoszulTraceFib_apply_section_contMDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieKoszulTraceFib_apply_section_contMDiff target :: scope.openDecls } }


omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem deTurckLieFirstOrderCoreFib_apply_section_contMDiff
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (Y : ContMDiffSection I (Tensor0SBundle.Tensor0SModel 3 ℝ E) ∞
      (fun x : M => Tensor0SBundle.Tensor0SSpace 3 I x)) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x
        (deTurckLieFirstOrderCoreFib (I := I) g₀ g₁ g_bg x (Y x))) := by
  classical
  have hS2 := deTurckLiePairTraceFib_apply_section_contMDiff (I := I) g₁
    deTurckLieFirstOrderPairPermInnerTwo
    (fun x => metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ x)
    (metricConnectionDifferenceLoweredFib_contMDiff (I := I) g₁ g₁ g₀) Y
  have hB := deTurckLiePairTraceFib_apply_section_contMDiff (I := I) g₁
    deTurckLieFirstOrderPairPermCorrection
    (fun x => metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g_bg x)
    (metricConnectionDifferenceLoweredFib_contMDiff (I := I) g₁ g₁ g_bg) Y
  have hpermY := domDomCongr_section_contMDiff_local (I := I) (d := 3)
    deTurckLieFirstOrderVecSlotPerm (fun x => Y x) Y.contMDiff
  have hT2 := interiorProductField_contMDiff (I := I) 2
    (fun x => Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
      (ContinuousMultilinearMap.domDomCongr deTurckLieFirstOrderVecSlotPerm
        (Tensor0SBundle.Tensor0SSpace.toModel (Y x)))) hpermY
    (PDE.DeTurck.deTurckVF (I := I) g₁ g₀)
  have hT3 := deTurckLiePairTraceFib_apply_section_contMDiff (I := I) g₁
    deTurckLieFirstOrderPairPermOuterZero
    (fun x => metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ x)
    (metricConnectionDifferenceLoweredFib_contMDiff (I := I) g₁ g₁ g₀) Y
  have hT4 := deTurckLieKoszulTraceFib_apply_section_contMDiff (I := I) g₀ g₁
    deTurckLieFirstOrderKoszulMidPerm Y
  have hT5 := deTurckLiePairTraceFib_apply_section_contMDiff (I := I) g₁
    deTurckLieFirstOrderPairPermOuterTwo
    (fun x => metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ x)
    (metricConnectionDifferenceLoweredFib_contMDiff (I := I) g₁ g₁ g₀) Y
  have hsum := ((((hS2.sub_section hB).sub_section hT2).sub_section hT3).sub_section
    hT4).sub_section hT5
  refine hsum.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x t) ?_
  rw [deTurckLieFirstOrderCoreFib]
  simp only [sub_apply, ContinuousLinearMap.comp_apply]
  rw [domDomCongrFibRank_apply]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderCoreFib_apply_section_contMDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderCoreFib_apply_section_contMDiff target :: scope.openDecls } }

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem deTurckLieFirstOrderFib_contMDiff (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 3 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 3 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 3 2 I z) x
        (deTurckLieFirstOrderFib (I := I) g₀ g₁ g_bg x)) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 3 ℝ E)
      (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 3 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
      (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun x : M => deTurckLieFirstOrderFib (I := I) g₀ g₁ g_bg x)
  intro Y
  have hW := interiorProductField_contMDiff (I := I) 2 (fun x => Y x) Y.contMDiff
    (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg)
  have hcore := deTurckLieFirstOrderCoreFib_apply_section_contMDiff (I := I) g₀ g₁ g_bg Y
  have hcoreswap := domDomCongr_section_contMDiff_local (I := I) (d := 2)
    (Equiv.swap (0 : Fin 2) 1)
    (fun x => deTurckLieFirstOrderCoreFib (I := I) g₀ g₁ g_bg x (Y x)) hcore
  have hS3 := deTurckLieKoszulTraceFib_apply_section_contMDiff (I := I) g₀ g₁
    deTurckLieFirstOrderKoszulZeroPerm Y
  have hsum := ((hW.add_section hcore).add_section hcoreswap).add_section hS3
  refine hsum.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x t) ?_
  rw [deTurckLieFirstOrderFib]
  simp only [add_apply, ContinuousLinearMap.comp_apply]
  rw [domDomCongrFibRank_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderFib_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderFib_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderFib_contMDiff ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderFib_contMDiff

noncomputable def deTurckLieFirstOrderCoeff (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 3 2 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 3 2 I x from deTurckLieFirstOrderFib (I := I) g₀ g₁ g_bg x)
      contMDiff_toFun := deTurckLieFirstOrderFib_contMDiff (I := I) g₀ g₁ g_bg }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderCoeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderCoeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderCoeff ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderCoeff


omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
@[simp] theorem deTurckLieFirstOrderCoeff_toSection (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    (deTurckLieFirstOrderCoeff (I := I) (M := M) g₀ g₁ g_bg).toSection x =
      (show Tensor0SBundle.TensorRSSpace 3 2 I x from
        deTurckLieFirstOrderFib (I := I) g₀ g₁ g_bg x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderCoeff_toSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderCoeff_toSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderCoeff_toSection ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieFirstOrderCoeff_toSection

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
