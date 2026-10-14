import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Naturality.CrossTensorCovariantDerivative
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.OpenChartTimeJets

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [CompleteSpace F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]

private local instance timeTensorSourceC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.timeTensorSourceC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.timeTensorSourceC1 target :: scope.openDecls } }
private local instance timeTensorTargetC1 : IsManifold J 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.timeTensorTargetC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.timeTensorTargetC1 target :: scope.openDecls } }

omit [CompleteSpace E] [CompleteSpace F] [T2Space M] [T2Space N] in
theorem timeTensorJets_pullbackCross
    (Phi : M ≃ₘ⟮I, J⟯ N) {times : Set ℝ} (htimes : UniqueDiffOn ℝ times)
    (A : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2)
    (B : ℕ → ℝ → Tensor0SField (I := J) (M := N) (n := ∞) 2)
    (hA : ∀ q t, t ∈ times → ∀ x : M,
      HasDerivWithinAt (fun s => A q s x) (A (q + 1) t x) times t)
    (hB : ∀ q t, t ∈ times → ∀ y : N,
      HasDerivWithinAt (fun s => B q s y) (B (q + 1) t y) times t)
    (hzero : ∀ t ∈ times, ∀ x : M, ∀ v : Fin 2 → TangentSpace I x,
      A 0 t x v = B 0 t (Phi x) (fun q => mfderiv I J Phi x (v q)))
    (q : ℕ) {t : ℝ} (ht : t ∈ times) (x : M) (v : Fin 2 → TangentSpace I x) :
    A q t x v = B q t (Phi x) (fun j => mfderiv I J Phi x (v j)) := by
  let w : Fin 2 → TangentSpace J (Phi x) := fun j => mfderiv I J Phi x (v j)
  let f : ℕ → ℝ → ℝ := fun q s => A q s x v
  let g : ℕ → ℝ → ℝ := fun q s => B q s (Phi x) w
  have hf (a : ℕ) (s : ℝ) (hs : s ∈ times) :
      HasDerivWithinAt (f a) (f (a + 1) s) times s :=
    (tensor0SEvalCLM (I := I) (x := x) v).hasFDerivAt.comp_hasDerivWithinAt s (hA a s hs x)
  have hg (a : ℕ) (s : ℝ) (hs : s ∈ times) :
      HasDerivWithinAt (g a) (g (a + 1) s) times s :=
    (tensor0SEvalCLM (I := J) (x := Phi x) w).hasFDerivAt.comp_hasDerivWithinAt s
      (hB a s hs (Phi x))
  exact scalar_time_towers_eq htimes f g hf hg (fun s hs => hzero s hs x v) q t ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.timeTensorJets_pullbackCross then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.timeTensorJets_pullbackCross"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.timeTensorJets_pullbackCross ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.timeTensorJets_pullbackCross


theorem mixedTensorJetNorm_pullbackCross [SigmaCompactSpace M]
    (Phi : M ≃ₘ⟮I, J⟯ N) {times : Set ℝ} (htimes : UniqueDiffOn ℝ times)
    (A : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2)
    (B : ℕ → ℝ → Tensor0SField (I := J) (M := N) (n := ∞) 2)
    (hA : ∀ q t, t ∈ times → ∀ x : M,
      HasDerivWithinAt (fun s => A q s x) (A (q + 1) t x) times t)
    (hB : ∀ q t, t ∈ times → ∀ y : N,
      HasDerivWithinAt (fun s => B q s y) (B (q + 1) t y) times t)
    (hzero : ∀ t ∈ times, ∀ x : M, ∀ v : Fin 2 → TangentSpace I x,
      A 0 t x v = B 0 t (Phi x) (fun q => mfderiv I J Phi x (v q)))
    (gcov gnorm : ℝ → SmoothRiemannianMetric J N)
    (a q : ℕ) {t : ℝ} (ht : t ∈ times) (x : M) :
    tensor02CovDerivNormWith a (A q t)
        (DifferentialGeometry.Diffeomorph.pullbackMetricCross (gcov t) Phi)
        (DifferentialGeometry.Diffeomorph.pullbackMetricCross (gnorm t) Phi) x =
      tensor02CovDerivNormWith a (B q t) (gcov t) (gnorm t) (Phi x) :=
  tensor02CovDerivNormWith_pullbackCross (gcov t) (gnorm t) Phi (A q t) (B q t)
    (timeTensorJets_pullbackCross Phi htimes A B hA hB hzero q ht) a x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.mixedTensorJetNorm_pullbackCross then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.mixedTensorJetNorm_pullbackCross"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.mixedTensorJetNorm_pullbackCross ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.mixedTensorJetNorm_pullbackCross

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
