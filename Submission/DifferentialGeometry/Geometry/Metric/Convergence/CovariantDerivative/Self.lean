import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Bounds
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Algebra
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Koszul.Formula
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Scaling

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open scoped _root_.Manifold _root_.ContDiff _root_.Topology
open _root_.Submission.DifferentialGeometry.Geometry.Connection

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

section FixedDomain

variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]

local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealHAddWithTopENatSomeTopOfNat_differentialGeometry_1 : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
  simpa using (inferInstance : IsManifold I (∞ : WithTop ℕ∞) M)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealHAddWithTopENatSomeTopOfNat_differentialGeometry_1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealHAddWithTopENatSomeTopOfNat_differentialGeometry_1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealHAddWithTopENatSomeTopOfNat_differentialGeometry_1 ``Submission.DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealHAddWithTopENatSomeTopOfNat_differentialGeometry_1

omit [SigmaCompactSpace M] in
private theorem covDeriv_self_one (g : SmoothRiemannianMetric I M) :
    metricCovDeriv (I := I) g g 1 = 0 := by
  refine DFunLike.ext _ _ (fun x => ?_)
  refine ContinuousMultilinearMap.ext (fun slots => ?_)
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (slots 0)
  have hcons : Fin.cons (X x) (Fin.tail slots) = slots := by
    rw [hX]
    exact Fin.cons_self_tail slots
  have h1 := metricCovDeriv_one_apply_section (I := I) g g X x (Fin.tail slots)
  have h0 : Tensor0SBundle.nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
      (leviCivitaConnectionOfMetric (I := I) g) X
      (metricCovDeriv (I := I) g g 0) x = 0 := by
    have hbase : metricCovDeriv (I := I) g g 0
        = Tensor0SBundle.metricTensorField (I := I) g := rfl
    rw [hbase]
    exact Tensor0SBundle.nabla_metric_zero (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) g
      (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g) X x
  calc metricCovDeriv (I := I) g g 1 x slots
      = metricCovDeriv (I := I) g g 1 x (Fin.cons (X x) (Fin.tail slots)) := by rw [hcons]
    _ = Tensor0SBundle.nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
          (leviCivitaConnectionOfMetric (I := I) g) X
          (metricCovDeriv (I := I) g g 0) x (Fin.tail slots) := h1
    _ = 0 := by rw [h0]; rfl
    _ = (0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (1 + 2)) x slots := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.covDeriv_self_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.covDeriv_self_one target :: scope.openDecls } }

omit [SigmaCompactSpace M] in
theorem covDeriv_self_succ (g : SmoothRiemannianMetric I M) (a : Nat) :
    metricCovDeriv (I := I) g g (a + 1) = 0 := by
  induction a with
  | zero => exact covDeriv_self_one (I := I) g
  | succ n ih =>
      rw [metricCovDeriv_succ, ih]
      have hz := metricCovDerivStep_smul (I := I) g (0 : Real) (n + 1)
        (0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (n + 1 + 2))
      rw [zero_smul, zero_smul] at hz
      exact hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.covDeriv_self_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.covDeriv_self_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.covDeriv_self_succ ``Submission.DifferentialGeometry.CheegerGromovCompactness.covDeriv_self_succ

omit [SigmaCompactSpace M] in
theorem covNorm_self_succ (g : SmoothRiemannianMetric I M) (a : Nat) (x : M) :
    metricCovDerivNorm (I := I) (a + 1) g g x = 0 := by
  have h := covDeriv_self_succ (I := I) g a
  simp only [metricCovDerivNorm]
  have hx0 : metricCovDeriv (I := I) g g (a + 1) x
      = (0 : Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (a + 1 + 2) x) := by
    rw [h]; rfl
  rw [hx0]
  have hzero : (0 : Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (a + 1 + 2) x)
      = (0 : Real) • (0 : Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (a + 1 + 2) x) := (zero_smul _ _).symm
  rw [hzero, Tensor0SBundle.sqrt_normSq0S_smul]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.covNorm_self_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.covNorm_self_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.covNorm_self_succ ``Submission.DifferentialGeometry.CheegerGromovCompactness.covNorm_self_succ

end FixedDomain

end CheegerGromovCompactness
end DifferentialGeometry
