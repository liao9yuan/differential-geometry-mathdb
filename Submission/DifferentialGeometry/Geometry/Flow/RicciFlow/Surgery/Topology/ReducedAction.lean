import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.MetricStep
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.SmoothAttainment

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M]

theorem reducedAction_eq_lLength {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := M) D) (T τ : ℝ) (γ : ℝ → M) :
    reducedAction S.base.metric T τ γ = lLength S T γ 0 τ := by
  unfold reducedAction lLength lDensity lSpeedSq lVelocity
  congr 1
  funext s
  change Real.sqrt s * (_ + Real.sqrt _ ^ 2) = _
  rw [Real.sq_sqrt (DifferentialGeometry.metric_inner_self_nonneg _ _ _)]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.reducedAction_eq_lLength then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.reducedAction_eq_lLength"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.reducedAction_eq_lLength ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.reducedAction_eq_lLength

def isRegularizedAdmissible (γ : ℝ → M) : Prop :=
  ∃ α : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 α ∧ squareRootReparametrization α = γ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isRegularizedAdmissible then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isRegularizedAdmissible"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isRegularizedAdmissible ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isRegularizedAdmissible

theorem reducedLength_eq_lCost {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := M) D) (T τ : ℝ) (x y : M) :
    reducedLength S.base.metric T isRegularizedAdmissible x τ y = lCost S T x y τ := by
  unfold reducedLength lCost
  apply congrArg _root_.InfSet.sInf
  ext r
  constructor
  · rintro ⟨γ,⟨α,hα,rfl⟩,h0,h1,hr⟩
    refine ⟨α,hα,?_,h1,?_⟩
    · simpa only [squareRootReparametrization,Real.sqrt_zero] using h0
    · rwa [reducedAction_eq_lLength] at hr
  · rintro ⟨α,hα,h0,h1,hr⟩
    refine ⟨squareRootReparametrization α,⟨α,hα,rfl⟩,?_,h1,?_⟩
    · simpa only [squareRootReparametrization,Real.sqrt_zero] using h0
    · rwa [reducedAction_eq_lLength]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.reducedLength_eq_lCost then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.reducedLength_eq_lCost"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.reducedLength_eq_lCost ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.reducedLength_eq_lCost

variable [T2Space M] [CompactSpace M]

theorem exists_reducedAction_minimizer_of_regular_interval {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := M) D) (hS : IsSolutionOn S)
    (T τ : ℝ) (hτ : 0 < τ) (hreg : _root_.Set.Icc (T - τ) T ⊆ D.regular)
    (x y : M) (α₀ : ℝ → M) (hα₀ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 α₀)
    (h₀ : α₀ 0 = x) (h₁ : α₀ (Real.sqrt τ) = y) :
    ∃ α : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ α ∧ α 0 = x ∧ α (Real.sqrt τ) = y ∧
      isRegularizedAdmissible (squareRootReparametrization α) ∧
      reducedAction S.base.metric T τ (squareRootReparametrization α) =
        reducedLength S.base.metric T isRegularizedAdmissible x τ y := by
  obtain ⟨α,hα,h0,h1,hmin⟩ := exists_contMDiff_lCost_minimizer S hS T τ hτ hreg x y α₀ hα₀ h₀ h₁
  refine ⟨α,hα,h0,h1,⟨α,hα.of_le (by simp),rfl⟩,?_⟩
  rw [reducedAction_eq_lLength,reducedLength_eq_lCost]
  exact hmin

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_reducedAction_minimizer_of_regular_interval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_reducedAction_minimizer_of_regular_interval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_reducedAction_minimizer_of_regular_interval ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_reducedAction_minimizer_of_regular_interval

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
