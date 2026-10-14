import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Sections
import Submission.DifferentialGeometry.Geometry.Connection.Laplacian.TensorConnLaplacian
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Identities.Ricci

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

open _root_.Submission.DifferentialGeometry.Geometry.Connection

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.FiberBundle _root_.NormedSpace _root_.Filter _root_.CovariantDerivative _root_.Submission.CovariantDerivative _root_.Submission.DifferentialGeometry.Geometry.Curvature.CovariantDerivative
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry
namespace Geometry
namespace Curvature

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Tensor0SBundle

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [FiniteDimensional ℝ F]

theorem riemannSec_eq_riemannOp_smooth
    (cov : CovariantDerivative I F V)
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {X Y : Π b : M, TangentSpace I b} {Z : Π b : M, V b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% Z)) :
    riemannSec cov X Y Z x = riemannOp cov x (X x) (Y x) (Z x) :=
  (riemannOp_apply_smooth (cov := cov) hX hY hZ).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.riemannSec_eq_riemannOp_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.riemannSec_eq_riemannOp_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.riemannSec_eq_riemannOp_smooth ``Submission.DifferentialGeometry.Geometry.Curvature.riemannSec_eq_riemannOp_smooth

theorem cov_commutator_eq_riemannOp_smooth
    (cov : CovariantDerivative I F V)
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {X Y : Π b : M, TangentSpace I b} {Z : Π b : M, V b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% Z)) :
    cov.toFun (covApply cov Y Z) x (X x) - cov.toFun (covApply cov X Z) x (Y x)
        - cov.toFun Z x (VectorField.mlieBracket I X Y x) =
      riemannOp cov x (X x) (Y x) (Z x) := by
  rw [← riemannSec_def cov X Y Z x]
  exact riemannSec_eq_riemannOp_smooth (cov := cov) hX hY hZ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.cov_commutator_eq_riemannOp_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.cov_commutator_eq_riemannOp_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.cov_commutator_eq_riemannOp_smooth ``Submission.DifferentialGeometry.Geometry.Curvature.cov_commutator_eq_riemannOp_smooth

end General

section TensorBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [T2Space M] [BoundarylessManifold I M]

omit [T2Space M] [BoundarylessManifold I M] in
noncomputable abbrev tensorCov (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    CovariantDerivative I (TensorRSModel r s ℝ E) (fun x : M => TensorRSSpace r s I x) :=
  TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensorCov then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensorCov"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensorCov ``Submission.DifferentialGeometry.Geometry.Curvature.tensorCov

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorRicciCommutator
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (X Y : Π b : M, TangentSpace I b) (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    (tensorCov (I := I) g r s).toFun
        (covApply (tensorCov (I := I) g r s) Y T) x (X x) -
      (tensorCov (I := I) g r s).toFun
        (covApply (tensorCov (I := I) g r s) X T) x (Y x) -
      (tensorCov (I := I) g r s).toFun T x (VectorField.mlieBracket I X Y x) =
      riemannSec (tensorCov (I := I) g r s) X Y T x :=
  (riemannSec_def (tensorCov (I := I) g r s) X Y T x).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensorRicciCommutator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensorRicciCommutator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensorRicciCommutator ``Submission.DifferentialGeometry.Geometry.Curvature.tensorRicciCommutator

omit [NeZero (Module.finrank ℝ E)] in
theorem ricci_identity_tensor_commutator_eq_riemannOp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {X Y : Π b : M, TangentSpace I b} {T : Π b : M, TensorRSSpace r s I b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) b (T b))) :
    (tensorCov (I := I) g r s).toFun
        (covApply (tensorCov (I := I) g r s) Y T) x (X x) -
      (tensorCov (I := I) g r s).toFun
        (covApply (tensorCov (I := I) g r s) X T) x (Y x) -
      (tensorCov (I := I) g r s).toFun T x (VectorField.mlieBracket I X Y x) =
      riemannOp (tensorCov (I := I) g r s) x (X x) (Y x) (T x) := by
  rw [tensorRicciCommutator (I := I) g r s X Y T x]
  exact riemannSec_eq_riemannOp_smooth (cov := tensorCov (I := I) g r s) hX hY hT

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.ricci_identity_tensor_commutator_eq_riemannOp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.ricci_identity_tensor_commutator_eq_riemannOp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.ricci_identity_tensor_commutator_eq_riemannOp ``Submission.DifferentialGeometry.Geometry.Curvature.ricci_identity_tensor_commutator_eq_riemannOp

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorRicciCommutator_swap
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (X Y : Π b : M, TangentSpace I b) (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    riemannSec (tensorCov (I := I) g r s) X Y T x =
      - riemannSec (tensorCov (I := I) g r s) Y X T x :=
  riemannSec_swap (tensorCov (I := I) g r s) X Y T x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensorRicciCommutator_swap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensorRicciCommutator_swap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensorRicciCommutator_swap ``Submission.DifferentialGeometry.Geometry.Curvature.tensorRicciCommutator_swap

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorRicciCommutator_self
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (X : Π b : M, TangentSpace I b) (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    riemannSec (tensorCov (I := I) g r s) X X T x = 0 :=
  riemannSec_self_eq_zero (tensorCov (I := I) g r s) X T x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensorRicciCommutator_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensorRicciCommutator_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensorRicciCommutator_self ``Submission.DifferentialGeometry.Geometry.Curvature.tensorRicciCommutator_self

noncomputable def tensorSecondCovDeriv
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (X Y : Π b : M, TangentSpace I b) (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    TensorRSSpace r s I x :=
  (tensorCov (I := I) g r s).toFun (covApply (tensorCov (I := I) g r s) Y T) x (X x) -
    (tensorCov (I := I) g r s).toFun T x ((LeviCivita (I := I) g).toFun Y x (X x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensorSecondCovDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensorSecondCovDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensorSecondCovDeriv ``Submission.DifferentialGeometry.Geometry.Curvature.tensorSecondCovDeriv

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tensorSecondCovDeriv_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (X Y : Π b : M, TangentSpace I b) (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    tensorSecondCovDeriv (I := I) g r s X Y T x =
      (tensorCov (I := I) g r s).toFun (covApply (tensorCov (I := I) g r s) Y T) x (X x) -
        (tensorCov (I := I) g r s).toFun T x ((LeviCivita (I := I) g).toFun Y x (X x)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensorSecondCovDeriv_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensorSecondCovDeriv_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensorSecondCovDeriv_def ``Submission.DifferentialGeometry.Geometry.Curvature.tensorSecondCovDeriv_def

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorSecondCovDeriv_antisymm_eq_riemannSec
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {X Y : Π b : M, TangentSpace I b} (T : Π b : M, TensorRSSpace r s I b) {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    tensorSecondCovDeriv (I := I) g r s X Y T x -
        tensorSecondCovDeriv (I := I) g r s Y X T x =
      riemannSec (tensorCov (I := I) g r s) X Y T x := by
  classical
  set cov := tensorCov (I := I) g r s with hcov_def
  have hbr : (LeviCivita (I := I) g).toFun Y x (X x) -
      (LeviCivita (I := I) g).toFun X x (Y x) = VectorField.mlieBracket I X Y x :=
    (CovariantDerivative.torsion_eq_zero_iff (cov := LeviCivita (I := I) g)).mp
      (LeviCivita_torsion_eq_zero (I := I) g) hX hY
  rw [tensorSecondCovDeriv_def, tensorSecondCovDeriv_def, riemannSec_def]
  have hsub : (cov.toFun T x ((LeviCivita (I := I) g).toFun Y x (X x)) -
        cov.toFun T x ((LeviCivita (I := I) g).toFun X x (Y x))) =
      cov.toFun T x (VectorField.mlieBracket I X Y x) := by
    rw [← map_sub (cov.toFun T x), hbr]
  rw [show
      (cov.toFun (covApply cov Y T) x (X x) -
          cov.toFun T x ((LeviCivita (I := I) g).toFun Y x (X x))) -
        (cov.toFun (covApply cov X T) x (Y x) -
          cov.toFun T x ((LeviCivita (I := I) g).toFun X x (Y x))) =
      (cov.toFun (covApply cov Y T) x (X x) - cov.toFun (covApply cov X T) x (Y x)) -
        (cov.toFun T x ((LeviCivita (I := I) g).toFun Y x (X x)) -
          cov.toFun T x ((LeviCivita (I := I) g).toFun X x (Y x))) from by abel]
  rw [hsub]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensorSecondCovDeriv_antisymm_eq_riemannSec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensorSecondCovDeriv_antisymm_eq_riemannSec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensorSecondCovDeriv_antisymm_eq_riemannSec ``Submission.DifferentialGeometry.Geometry.Curvature.tensorSecondCovDeriv_antisymm_eq_riemannSec

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorSecondCovDeriv_antisymm_eq_riemannOp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {X Y : Π b : M, TangentSpace I b} {T : Π b : M, TensorRSSpace r s I b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) b (T b))) :
    tensorSecondCovDeriv (I := I) g r s X Y T x -
        tensorSecondCovDeriv (I := I) g r s Y X T x =
      riemannOp (tensorCov (I := I) g r s) x (X x) (Y x) (T x) := by
  rw [tensorSecondCovDeriv_antisymm_eq_riemannSec (I := I) g r s T
        ((hX x).mdifferentiableAt (by simp)) ((hY x).mdifferentiableAt (by simp))]
  exact riemannSec_eq_riemannOp_smooth (cov := tensorCov (I := I) g r s) hX hY hT

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensorSecondCovDeriv_antisymm_eq_riemannOp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensorSecondCovDeriv_antisymm_eq_riemannOp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensorSecondCovDeriv_antisymm_eq_riemannOp ``Submission.DifferentialGeometry.Geometry.Curvature.tensorSecondCovDeriv_antisymm_eq_riemannOp

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem rawTensorConnLap_eq_frame_trace_secondCovDeriv
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    rawTensorConnLap (I := I) g r s T x =
      ∑ i : Fin (Module.finrank ℝ E),
        tensorSecondCovDeriv (I := I) g r s
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) T x := by
  rw [rawTensorConnLap_def]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [tensorSecondCovDeriv_def]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.rawTensorConnLap_eq_frame_trace_secondCovDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.rawTensorConnLap_eq_frame_trace_secondCovDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.rawTensorConnLap_eq_frame_trace_secondCovDeriv ``Submission.DifferentialGeometry.Geometry.Curvature.rawTensorConnLap_eq_frame_trace_secondCovDeriv

end TensorBundle

end Curvature
end Geometry
end DifferentialGeometry
