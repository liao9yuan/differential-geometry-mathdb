import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.CurvatureContinuity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.Isometry
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.InverseMetric

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Set _root_.Submission.Set _root_.Filter
open _root_.Submission.DifferentialGeometry.Analysis.ODE
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree
open scoped _root_.BigOperators _root_.Topology _root_.NNReal _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

omit [SigmaCompactSpace M] in
theorem ricciAt_continuousOn_time
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    (x : M) (v w : TangentSpace I x) :
    ContinuousOn (fun t : ℝ => S.ricciAt t x (vec2 v w)) (Set.Icc 0 T) := by
  exact hS.continuousOn_ricciAt x v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ricciAt_continuousOn_time then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricciAt_continuousOn_time"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricciAt_continuousOn_time ``Submission.DifferentialGeometry.PDE.RicciFlow.ricciAt_continuousOn_time

noncomputable def solutionUhlenbeckIota
    {T : ℝ} (hT : 0 < T) [I.Boundaryless]
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] [Nonempty Idx]
    (basisAt : ∀ x : M, Module.Basis Idx Real (TangentSpace I x)) :
    MatrixComp M Idx :=
  Classical.choose (uhlenbeckIota_isometry (I := I) (M := M) hT S hS
    (solutionInverseMetricComponents (I := I) (M := M) S basisAt)
    (fun x i j => solutionInverseMetricComponents_entry_continuousOn
      (I := I) (M := M) hT S hS basisAt x i j)
    (fun x v w => ricciAt_continuousOn_time (I := I) (M := M) hT S hS x v w)
    (fun a x => basisAt x a)
    (fun t x i j => solutionInverseMetricComponents_mul_metric
      (I := I) (M := M) S basisAt t x i j)
    (fun t x i j => solutionInverseMetricComponents_symm
      (I := I) (M := M) S basisAt t x i j)
    (fun a k => if a = k then 1 else 0))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.solutionUhlenbeckIota then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.solutionUhlenbeckIota"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.solutionUhlenbeckIota ``Submission.DifferentialGeometry.PDE.RicciFlow.solutionUhlenbeckIota

omit [SigmaCompactSpace M] in
theorem solutionUhlenbeckIota_spec
    {T : ℝ} (hT : 0 < T) [I.Boundaryless]
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] [Nonempty Idx]
    (basisAt : ∀ x : M, Module.Basis Idx Real (TangentSpace I x)) :
    (∀ x : M, ∀ a k : Idx,
      solutionUhlenbeckIota hT S hS basisAt 0 x a k = if a = k then 1 else 0) ∧
    (∀ x : M, ContinuousOn
      (fun t : ℝ => solutionUhlenbeckIota hT S hS basisAt t x) (Set.Icc 0 T)) ∧
    (∀ t : ℝ, t ∈ Set.Ico 0 T → ∀ x : M, ∀ a k : Idx,
      HasDerivWithinAt
        (fun s : ℝ => solutionUhlenbeckIota hT S hS basisAt s x a k)
        (∑ l : Idx,
          uhlenbeckRupOfSolution (I := I) S (solutionInverseMetricComponents S basisAt)
              (fun a x => basisAt x a) t x l k *
            solutionUhlenbeckIota hT S hS basisAt t x a l)
        (Set.Ici 0) t) ∧
    FrameRicciODEInFrameOn (D := RealTimeInterval.closed 0 T hT.le)
      (solutionUhlenbeckIota hT S hS basisAt)
      (uhlenbeckRupOfSolution (I := I) S (solutionInverseMetricComponents S basisAt)
        (fun a x => basisAt x a)) ∧
    (∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Idx,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a))
        (solutionUhlenbeckIota hT S hS basisAt) t x a b =
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a))
        (solutionUhlenbeckIota hT S hS basisAt) 0 x a b) := by
  classical
  exact Classical.choose_spec (uhlenbeckIota_isometry (I := I) (M := M) hT S hS
    (solutionInverseMetricComponents (I := I) (M := M) S basisAt)
    (fun x i j => solutionInverseMetricComponents_entry_continuousOn
      (I := I) (M := M) hT S hS basisAt x i j)
    (fun x v w => ricciAt_continuousOn_time (I := I) (M := M) hT S hS x v w)
    (fun a x => basisAt x a)
    (fun t x i j => solutionInverseMetricComponents_mul_metric
      (I := I) (M := M) S basisAt t x i j)
    (fun t x i j => solutionInverseMetricComponents_symm
      (I := I) (M := M) S basisAt t x i j)
    (fun a k => if a = k then 1 else 0))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.solutionUhlenbeckIota_spec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.solutionUhlenbeckIota_spec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.solutionUhlenbeckIota_spec ``Submission.DifferentialGeometry.PDE.RicciFlow.solutionUhlenbeckIota_spec

omit [SigmaCompactSpace M] in
theorem solutionUhlenbeckIota_identity_initial_gram
    {T : ℝ} (hT : 0 < T) [I.Boundaryless]
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))
    (t : ℝ) (ht : t ∈ Set.Icc 0 T) (x : M) (a b : Fin 3) :
    movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a))
      (solutionUhlenbeckIota hT S hS basisAt) t x a b = if a = b then 1 else 0 := by
  classical
  have hspec := solutionUhlenbeckIota_spec (I := I) (M := M) hT S hS basisAt
  have hgram := hspec.2.2.2.2 t ht x a b
  rw [hgram]
  have hiota0 := hspec.1 x
  have horth : ∀ i j : Fin 3,
      (S.base.metric 0).inner x (basisAt x i) (basisAt x j) = if i = j then 1 else 0 := by
    intro i j
    simpa [delta3] using horth0 x i j
  simp [movingFrameGramInFrame, hiota0, horth, Finset.sum_ite_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.solutionUhlenbeckIota_identity_initial_gram then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.solutionUhlenbeckIota_identity_initial_gram"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.solutionUhlenbeckIota_identity_initial_gram ``Submission.DifferentialGeometry.PDE.RicciFlow.solutionUhlenbeckIota_identity_initial_gram

omit [SigmaCompactSpace M] in
theorem exists_uhlenbeckFrame_of_finrank
    {T : ℝ} (hT : 0 < T) [I.Boundaryless]
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3) :
    ∃ basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x),
      (∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x)) ∧
      ∃ iota : MatrixComp M (Fin 3),
        (∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0) ∧
        FrameRicciODEInFrameOn (D := RealTimeInterval.closed 0 T hT.le) iota
          (uhlenbeckRupOfSolution (I := I) S
            (solutionInverseMetricComponents S basisAt) (fun a x => basisAt x a)) ∧
        (∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
          movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a))
            iota t x a b = if a = b then 1 else 0) := by
  classical
  let basisAt₀ : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x) :=
    fun x => Classical.choose (exists_orthonormalBasisAt (I := I) (S.base.metric 0) x (hdim x))
  have horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt₀ x) := by
    intro x
    exact Classical.choose_spec (exists_orthonormalBasisAt (I := I) (S.base.metric 0) x (hdim x))
  let iota : MatrixComp M (Fin 3) := solutionUhlenbeckIota hT S hS basisAt₀
  have hspec := solutionUhlenbeckIota_spec (I := I) (M := M) hT S hS basisAt₀
  refine ⟨basisAt₀, horth0, iota, ?_, ?_, ?_⟩
  · intro x a k
    dsimp [iota]
    exact hspec.1 x a k
  · dsimp [iota]
    exact hspec.2.2.2.1
  · intro t ht x a b
    dsimp [iota]
    exact solutionUhlenbeckIota_identity_initial_gram
      (I := I) (M := M) hT S hS basisAt₀ horth0 t ht x a b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.exists_uhlenbeckFrame_of_finrank then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.exists_uhlenbeckFrame_of_finrank"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.exists_uhlenbeckFrame_of_finrank ``Submission.DifferentialGeometry.PDE.RicciFlow.exists_uhlenbeckFrame_of_finrank

end DifferentialGeometry.PDE.RicciFlow
