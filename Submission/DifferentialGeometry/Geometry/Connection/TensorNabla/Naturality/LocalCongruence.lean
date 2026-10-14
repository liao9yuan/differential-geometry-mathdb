import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.TensorRS.Basic
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.CovariantDerivative _root_.Submission.CovariantDerivative _root_.Submission.DifferentialGeometry.Geometry.Curvature.CovariantDerivative _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff


namespace DifferentialGeometry
namespace Geometry
namespace Connection

open _root_.Submission.DifferentialGeometry.Integral.Measure

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [BoundarylessManifold I M]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorRSCovariantDerivative_congr_of_eventuallyEq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {σ σ' : Π b : M, TensorRSSpace r s I b}
    {x : M} (hagree : ∀ᶠ y in 𝓝 x, σ y = σ' y)
    (hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
            (fun y : M =>
              TotalSpace.mk' (TensorRSModel r s ℝ E) y (σ y)) x)
    (hσ' : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
            (fun y : M =>
              TotalSpace.mk' (TensorRSModel r s ℝ E) y (σ' y)) x) :
    (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)).toFun σ x =
      (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)).toFun σ' x := by
  set cov := TensorRSNabla.tensorRSCovariantDerivative I M r s
    (LeviCivita (I := I) g) with hcov_def
  exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    (σ := σ) (σ' := σ') (x := x)
    hσ hσ' Filter.univ_mem hagree

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensorRSCovariantDerivative_congr_of_eventuallyEq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensorRSCovariantDerivative_congr_of_eventuallyEq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensorRSCovariantDerivative_congr_of_eventuallyEq ``Submission.DifferentialGeometry.Geometry.Connection.tensorRSCovariantDerivative_congr_of_eventuallyEq

end Connection
end Geometry
end DifferentialGeometry

end
