import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.JointRegularity
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.NormSquaredTime
import Mathlib.Topology.Order.Lattice

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Filter
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Operator
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.SolutionOn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] {D : RealTimeInterval}

theorem scalar_time_deriv_contMDiffOn (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => deriv (fun t => S.scalar t z.2) z.1)
      (D.regular ×ˢ (_root_.Set.univ : Set M)) := by
  intro z hz
  exact (timeDeriv_smoothAt
    ((scalar_joint S hS).contMDiffAt
      ((D.regular_isOpen.prod isOpen_univ).mem_nhds hz)) (by simp)).contMDiffWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar_time_deriv_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar_time_deriv_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar_time_deriv_contMDiffOn ``Submission.DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar_time_deriv_contMDiffOn

theorem scalar_time_derivWithin_Iic_continuousOn
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) :
    ContinuousOn
      (fun z : ℝ × M => derivWithin (fun t => S.scalar t z.2) (_root_.Set.Iic z.1) z.1)
      (D.regular ×ˢ (_root_.Set.univ : Set M)) := by
  apply (S.scalar_time_deriv_contMDiffOn hS).continuousOn.congr
  intro z hz
  exact ((hS.scalarTime (D.regular_subset hz.1) Subset.rfl z.2).differentiableAt
    (D.regular_mem_nhds hz.1)).derivWithin (uniqueDiffWithinAt_Iic z.1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar_time_derivWithin_Iic_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar_time_derivWithin_Iic_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar_time_derivWithin_Iic_continuousOn ``Submission.DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar_time_derivWithin_Iic_continuousOn

theorem scalar_time_derivWithin_Iic_residual_continuousOn
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (C q : ℝ) :
    ContinuousOn
      (fun z : ℝ × M => |derivWithin (fun t => S.scalar t z.2) (_root_.Set.Iic z.1) z.1| -
        C * (_root_.Max.max q (S.scalar z.1 z.2)) ^ 2)
      (D.regular ×ˢ (_root_.Set.univ : Set M)) := by
  exact (S.scalar_time_derivWithin_Iic_continuousOn hS).abs.sub
    (continuousOn_const.mul ((continuousOn_const.sup (scalar_joint S hS).continuousOn).pow 2))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar_time_derivWithin_Iic_residual_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar_time_derivWithin_Iic_residual_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar_time_derivWithin_Iic_residual_continuousOn ``Submission.DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar_time_derivWithin_Iic_residual_continuousOn

theorem scalar_gradient_norm_sq_contMDiffOn
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) :
    ContMDiffOn (𝓘(ℝ).prod I) 𝓘(ℝ) ∞
      (fun p : ℝ × M => (S.base.metric p.1).inner p.2
        (gradientFun (S.base.metric p.1) (S.scalar p.1) p.2)
        (gradientFun (S.base.metric p.1) (S.scalar p.1) p.2))
      (D.regular ×ˢ (_root_.Set.univ : Set M)) := by
  exact gradSq_joint S.family.metric D.regular_isOpen
    (fun α i j => hS.smoothMetric.chartGramMatrix_contDiffOn
      (G := S.family) Subset.rfl α i j)
    S.scalar (scalar_joint S hS)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar_gradient_norm_sq_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar_gradient_norm_sq_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar_gradient_norm_sq_contMDiffOn ``Submission.DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar_gradient_norm_sq_contMDiffOn

theorem scalar_gradient_norm_sq_residual_continuousOn
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (C q : ℝ) :
    ContinuousOn
      (fun z : ℝ × M => (S.base.metric z.1).inner z.2
        (gradientFun (S.base.metric z.1) (S.scalar z.1) z.2)
        (gradientFun (S.base.metric z.1) (S.scalar z.1) z.2) -
          C ^ 2 * (_root_.Max.max q (S.scalar z.1 z.2)) ^ 3)
      (D.regular ×ˢ (_root_.Set.univ : Set M)) := by
  exact (S.scalar_gradient_norm_sq_contMDiffOn hS).continuousOn.sub
    (continuousOn_const.mul ((continuousOn_const.sup (scalar_joint S hS).continuousOn).pow 3))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar_gradient_norm_sq_residual_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar_gradient_norm_sq_residual_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar_gradient_norm_sq_residual_continuousOn ``Submission.DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar_gradient_norm_sq_residual_continuousOn

theorem scalar_derivative_residual_continuousOn
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (C q : ℝ) :
    ContinuousOn
      (fun z : ℝ × M => _root_.Max.max
        ((S.base.metric z.1).inner z.2
          (gradientFun (S.base.metric z.1) (S.scalar z.1) z.2)
          (gradientFun (S.base.metric z.1) (S.scalar z.1) z.2) -
            C ^ 2 * (_root_.Max.max q (S.scalar z.1 z.2)) ^ 3)
        (|derivWithin (fun t => S.scalar t z.2) (_root_.Set.Iic z.1) z.1| -
          C * (_root_.Max.max q (S.scalar z.1 z.2)) ^ 2))
      (D.regular ×ˢ (_root_.Set.univ : Set M)) :=
  (S.scalar_gradient_norm_sq_residual_continuousOn hS C q).sup
    (S.scalar_time_derivWithin_Iic_residual_continuousOn hS C q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar_derivative_residual_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar_derivative_residual_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar_derivative_residual_continuousOn ``Submission.DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar_derivative_residual_continuousOn

end DifferentialGeometry.PDE.RicciFlow.SolutionOn

end
