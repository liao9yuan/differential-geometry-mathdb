import Submission.DifferentialGeometry.Geometry.Curvature.RoughLaplacian.MovingFrame.RemainderCarrierSection
import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.BracketDivergenceForm
import Submission.DifferentialGeometry.Geometry.Connection.MetricCompatibility.Commutation.SecondOrder
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Identities.ContractedBianchi

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

open _root_.Submission.DifferentialGeometry.Geometry.Connection

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.MeasureTheory
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry
namespace Geometry
namespace Curvature

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance _root_.Submission.DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

omit [CompactSpace M] in
theorem frameSummand_leadingSlot_secondOrder_commutation_orthoFrame
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    tensor0SCurry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          tensorSecondCovDeriv (I := I) g 0 (s + 1)
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
            (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x)
          (unitZeroSec (I := I) (M := M) x)) (smoothOrthoFrame (I := I) g x i x) -
      tensor0SCurry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          covGradBundleEquiv (I := I) (M := M) 0 s x
            ((tensorCov (I := I) g 0 s).toFun
              (fun y : M => tensorSecondCovDeriv (I := I) g 0 s
                (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
                (fun z : M => S.toSection z) y) x))
          (unitZeroSec (I := I) (M := M) x)) (smoothOrthoFrame (I := I) g x i x) =
      nablaTensorCurvSec (I := I) g
          (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
          (smoothOrthoFrame (I := I) g x i)
          (unitEvalSection (I := I) (M := M) g s S) x
        + (riemannSec (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
              (covApply (LeviCivita (I := I) g)
                (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i))
              (smoothOrthoFrame (I := I) g x i)
              (unitEvalSection (I := I) (M := M) g s S) x
            + riemannSec (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
              (smoothOrthoFrame (I := I) g x i)
              (covApply (LeviCivita (I := I) g)
                (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i))
              (unitEvalSection (I := I) (M := M) g s S) x
            + (2 : ℝ) • riemannSec
              (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
              (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
              (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
                (smoothOrthoFrame (I := I) g x i)
                (unitEvalSection (I := I) (M := M) g s S)) x)
        + secondOrderChristoffelResidual (I := I) g
            (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
            (unitEvalSection (I := I) (M := M) g s S) x := by
  have hB := smoothOrthoFrame_smooth (I := I) (M := M) g x i
  exact covGrad_covDeriv_leadingSlot_secondOrder_commutation (I := I) (M := M) g s S hB hB x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.frameSummand_leadingSlot_secondOrder_commutation_orthoFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.frameSummand_leadingSlot_secondOrder_commutation_orthoFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.frameSummand_leadingSlot_secondOrder_commutation_orthoFrame ``Submission.DifferentialGeometry.Geometry.Curvature.frameSummand_leadingSlot_secondOrder_commutation_orthoFrame

omit [CompactSpace M] [I.Boundaryless] in
theorem frame_cyclic_second_bianchi_orthoFrame
    (g : SmoothRiemannianMetric I M)
    {Z W : Π b : M, TangentSpace I b} {x : M}
    (i : Fin (Module.finrank ℝ E))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W)) :
    nablaCurvSec (LeviCivita (I := I) g)
        (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) Z W x +
      nablaCurvSec (LeviCivita (I := I) g)
        (smoothOrthoFrame (I := I) g x i) Z (smoothOrthoFrame (I := I) g x i) W x +
      nablaCurvSec (LeviCivita (I := I) g)
        Z (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) W x = 0 := by
  have hB := smoothOrthoFrame_smooth (I := I) (M := M) g x i
  exact second_bianchi_levi_civita_metric (I := I) (M := M) g hB hB hZ hW

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.frame_cyclic_second_bianchi_orthoFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.frame_cyclic_second_bianchi_orthoFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.frame_cyclic_second_bianchi_orthoFrame ``Submission.DifferentialGeometry.Geometry.Curvature.frame_cyclic_second_bianchi_orthoFrame

omit [CompactSpace M] [I.Boundaryless] in
theorem frameSummed_contracted_second_bianchi_eq_half_nablaScalar
    (g : SmoothRiemannianMetric I M)
    {V : Π b : M, TangentSpace I b} {x : M}
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V)) :
    ∑ j, nablaRicci (I := I) g
        (smoothOrthoFrame (I := I) g x j) (smoothOrthoFrame (I := I) g x j) V x =
      1 / 2 * nablaScalar (I := I) g V x := by
  exact contracted_second_bianchi (I := I) (M := M) g hV

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.frameSummed_contracted_second_bianchi_eq_half_nablaScalar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.frameSummed_contracted_second_bianchi_eq_half_nablaScalar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.frameSummed_contracted_second_bianchi_eq_half_nablaScalar ``Submission.DifferentialGeometry.Geometry.Curvature.frameSummed_contracted_second_bianchi_eq_half_nablaScalar

noncomputable def christoffelResidualPairingFib
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (i : Fin (Module.finrank ℝ E)) : ℝ :=
  covariantTensorInnerPointwise (I := I) (M := M) s g x
    (Tensor0SSpace.toModel
      (secondOrderChristoffelResidual (I := I) g
        (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
        (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
        (unitEvalSection (I := I) (M := M) g s S) x))
    (Tensor0SSpace.toModel
      (tensor0SCurry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g 0 s S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) (smoothOrthoFrame (I := I) g x i x)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.christoffelResidualPairingFib then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.christoffelResidualPairingFib"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.christoffelResidualPairingFib ``Submission.DifferentialGeometry.Geometry.Curvature.christoffelResidualPairingFib

end Curvature
end Geometry
end DifferentialGeometry

end
