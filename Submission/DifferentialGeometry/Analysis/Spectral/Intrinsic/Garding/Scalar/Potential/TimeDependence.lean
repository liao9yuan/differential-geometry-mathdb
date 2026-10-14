import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.Scalar.Potential.Basic
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Parametric.TimeDependentApplication

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

open _root_.Submission.DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete Real E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

theorem scalarPot_dyn_fin
    (q : SmoothRiemannianMetric I M)
    (zeta : Real → C^∞⟮I, M; Real⟯) {S : Set Real} (hS : IsOpen S)
    (hzeta : ContMDiffOn (I.prod 𝓘(Real, Real)) 𝓘(Real, Real) ∞
      (fun p : M × Real => (zeta p.2 : M → Real) p.1)
      ((Set.univ : Set M) ×ˢ S))
    (m k : ℕ)
    (U : Real → TensorHs (I := I) (M := M) q 0 0 (m : Real))
    (hU : ContDiffOn Real k U S) :
    ContDiffOn Real k
      (fun t => scalarPotHs (I := I) (M := M) q (zeta t) m (U t)) S := by
  have hcoeff := scalarCc_joint (I := I) (M := M) q zeta hzeta
  have happ := appHs_dyn_fin (I := I) (M := M) q 0 0 m k
    (fun t => scalarCc (I := I) (M := M) q (zeta t)) hS hcoeff U hU
  refine happ.congr ?_
  intro t ht
  exact scalarPotHs_app (I := I) (M := M) q (zeta t) m (U t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.scalarPot_dyn_fin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.scalarPot_dyn_fin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.scalarPot_dyn_fin ``Submission.DifferentialGeometry.Analysis.Spectral.scalarPot_dyn_fin

theorem scalarPot_dyn_cd
    (q : SmoothRiemannianMetric I M)
    (zeta : Real → C^∞⟮I, M; Real⟯) {S : Set Real} (hS : IsOpen S)
    (hzeta : ContMDiffOn (I.prod 𝓘(Real, Real)) 𝓘(Real, Real) ∞
      (fun p : M × Real => (zeta p.2 : M → Real) p.1)
      ((Set.univ : Set M) ×ˢ S))
    (m : ℕ)
    (U : Real → TensorHs (I := I) (M := M) q 0 0 (m : Real))
    (hU : ContDiffOn Real ∞ U S) :
    ContDiffOn Real ∞
      (fun t => scalarPotHs (I := I) (M := M) q (zeta t) m (U t)) S := by
  rw [contDiffOn_infty] at hU ⊢
  intro k
  exact scalarPot_dyn_fin (I := I) (M := M) q zeta hS hzeta m k U (hU k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.scalarPot_dyn_cd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.scalarPot_dyn_cd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.scalarPot_dyn_cd ``Submission.DifferentialGeometry.Analysis.Spectral.scalarPot_dyn_cd

end Spectral
end Analysis
end DifferentialGeometry

end
