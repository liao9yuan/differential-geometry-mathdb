import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Naturality.PullbackCross
import Submission.DifferentialGeometry.Geometry.Curvature.Algebraic.CurvatureOperatorConeMetric

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [CompleteSpace F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [T2Space N]

private local instance crossModelCurvatureSourceC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossModelCurvatureSourceC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossModelCurvatureSourceC1 target :: scope.openDecls } }

private local instance crossModelCurvatureTargetC1 : IsManifold J 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossModelCurvatureTargetC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossModelCurvatureTargetC1 target :: scope.openDecls } }

private theorem metricRm04_pullbackCross_apply_slots
    (g : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N)
    (x : M) (v : Fin 4 → TangentSpace I x) :
    metricRm04At (I := I) (Diffeomorph.pullbackMetricCross g Phi) x v =
      metricRm04At (I := J) g (Phi x)
        (fun i => mfderiv I J (Phi : M → N) x (v i)) := by
  have hsrc : vec4 (v 0) (v 1) (v 2) (v 3) = v := by
    funext i
    fin_cases i <;> rfl
  have hdst :
      vec4 (mfderiv I J (Phi : M → N) x (v 0))
          (mfderiv I J (Phi : M → N) x (v 1))
          (mfderiv I J (Phi : M → N) x (v 2))
          (mfderiv I J (Phi : M → N) x (v 3)) =
        (fun i : Fin 4 => mfderiv I J (Phi : M → N) x (v i)) := by
    funext i
    fin_cases i <;> rfl
  simpa only [metricRm04StandardAt_apply, hsrc, hdst] using
    metricRm04Standard_pullbackCross (I := I) (J := J) g Phi x
      (v 0) (v 1) (v 2) (v 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricRm04_pullbackCross_apply_slots
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricRm04_pullbackCross_apply_slots target :: scope.openDecls } }

theorem metricRmNormSq_pullbackCross [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N) (x : M) :
    normSq0S (I := I) (Diffeomorph.pullbackMetricCross g Phi) x 4
        (metricRm04At (I := I) (Diffeomorph.pullbackMetricCross g Phi) x) =
      normSq0S (I := J) g (Phi x) 4 (metricRm04At (I := J) g (Phi x)) := by
  classical
  obtain ⟨basis, hON⟩ :=
    exists_orthonormal_basis (I := I) (Diffeomorph.pullbackMetricCross g Phi) x
  exact normSq0S_pullbackCross_eval_of_orthonormal (I := I) (J := J)
    g Phi x 4 basis hON
    (metricRm04At (I := I) (Diffeomorph.pullbackMetricCross g Phi) x)
    (metricRm04At (I := J) g (Phi x))
    (metricRm04_pullbackCross_apply_slots g Phi x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricRmNormSq_pullbackCross then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricRmNormSq_pullbackCross"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricRmNormSq_pullbackCross ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricRmNormSq_pullbackCross

section CurvatureOperator

private local instance crossModelCurvatureSourceC2 : IsManifold I 2 M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossModelCurvatureSourceC2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossModelCurvatureSourceC2 target :: scope.openDecls } }

private local instance crossModelCurvatureTargetC2 : IsManifold J 2 N :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossModelCurvatureTargetC2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossModelCurvatureTargetC2 target :: scope.openDecls } }

private local instance crossModelCurvatureSourceC3 : IsManifold I 3 M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossModelCurvatureSourceC3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossModelCurvatureSourceC3 target :: scope.openDecls } }

private local instance crossModelCurvatureTargetC3 : IsManifold J 3 N :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossModelCurvatureTargetC3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossModelCurvatureTargetC3 target :: scope.openDecls } }

theorem metricCurvatureOperatorNonnegative_pullbackCross
    (g : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N) (x : M)
    (hR : metricAlgebraicCurvatureTensorAt (I := J) g (Phi x) ∈
      algebraicCurvatureOperatorNonnegativeCone (I := J)) :
    metricAlgebraicCurvatureTensorAt (I := I)
        (Diffeomorph.pullbackMetricCross g Phi) x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) := by
  apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
    (I := I) (Diffeomorph.pullbackMetricCross g Phi) x).mpr
  intro n c v w
  have htest :=
    (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
      (I := J) g (Phi x)).mp hR n c
        (fun i => mfderiv I J (Phi : M → N) x (v i))
        (fun i => mfderiv I J (Phi : M → N) x (w i))
  simpa only [metricRm04Standard_pullbackCross] using htest

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricCurvatureOperatorNonnegative_pullbackCross then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricCurvatureOperatorNonnegative_pullbackCross"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricCurvatureOperatorNonnegative_pullbackCross ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricCurvatureOperatorNonnegative_pullbackCross

end CurvatureOperator

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
