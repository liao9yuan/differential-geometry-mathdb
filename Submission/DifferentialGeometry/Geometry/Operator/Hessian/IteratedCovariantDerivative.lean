import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Components
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Naturality.SlotPermutation
import Submission.DifferentialGeometry.Geometry.Operator.Hessian.Trace.Realization

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Tensor.RSTensor
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsManifold I 1 M] [IsManifold I 2 M] [T2Space M]

theorem iterCov_zeroTensor_one_eq_duSec
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 0)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞) f)
    (hA : ∀ y, A y Fin.elim0 = f y) :
    iterCov (I := I) g 0 A 1 = duSec (I := I) f hf := by
  apply Tensor0SBundle.totalNabla0SRealizes_unique (iterCov_realizes (I := I) g A 0)
  change TotalNabla0SRealizes (I := I) 0 (leviCivitaConnectionOfMetric (I := I) g)
    A (duSec (I := I) f hf)
  intro X x slots
  have hslots : slots = Fin.elim0 := funext fun i => Fin.elim0 i
  subst slots
  have hcons : Fin.cons (X x) (Fin.elim0 : Fin 0 → TangentSpace I x) =
      fun _ : Fin 1 => X x := by
    funext i
    fin_cases i
    rfl
  rw [hcons, duSec_apply, differential1FormFun_apply_eq_mvfderiv]
  let V : Fin 0 → ContMDiffSection I E (∞ : WithTop ℕ∞)
    (TangentSpace I : M → Type _) := fun i => i.elim0
  have heval : (fun p => A p (fun a => V a p)) = f := by
    funext p
    exact (congrArg (A p) (Subsingleton.elim _ _)).trans (hA p)
  have hempty : (fun a => V a x) = (Fin.elim0 : Fin 0 → TangentSpace I x) :=
    Subsingleton.elim _ _
  have hnabla := nabla0SFun_eval_smooth_slots (I := I)
    (leviCivitaConnectionOfMetric (I := I) g) X V A x
  simpa only [hempty, heval, Finset.univ_eq_empty, Finset.sum_empty, sub_zero] using
    hnabla.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.iterCov_zeroTensor_one_eq_duSec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.iterCov_zeroTensor_one_eq_duSec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.iterCov_zeroTensor_one_eq_duSec ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.iterCov_zeroTensor_one_eq_duSec

theorem iterCov_zeroTensor_two_eq_hessianSec
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 0)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞) f)
    (hA : ∀ y, A y Fin.elim0 = f y) :
    iterCov (I := I) g 0 A 2 =
      hessianSec (I := I) (leviCivitaConnectionOfMetric (I := I) g)
        (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I) g) f hf := by
  rw [iterCov_succ, iterCov_zeroTensor_one_eq_duSec (I := I) g A f hf hA]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.iterCov_zeroTensor_two_eq_hessianSec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.iterCov_zeroTensor_two_eq_hessianSec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.iterCov_zeroTensor_two_eq_hessianSec ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.iterCov_zeroTensor_two_eq_hessianSec

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
