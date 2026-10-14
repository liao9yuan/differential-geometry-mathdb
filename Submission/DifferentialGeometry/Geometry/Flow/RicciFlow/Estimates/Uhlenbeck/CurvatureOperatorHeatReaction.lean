import Submission.DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Convex.Componentwise
import Submission.DifferentialGeometry.Analysis.InnerProductSpace.MatrixEuclidean
import Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.LeastEigenvalue
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.Frame

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle _root_.Submission.Bundle _root_.Set
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic
open _root_.Submission.DifferentialGeometry.Analysis.InnerProductSpace
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree
open scoped _root_.Manifold _root_.ContDiff _root_.Topology _root_.RealInnerProductSpace _root_.BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

noncomputable def uhlenbeckCurvatureOperatorMatrix
    (pulledRm : FourComp M (Fin 3)) : Real → M → EuclideanSpace ℝ (Fin 3 × Fin 3) :=
  fun t x => WithLp.toLp 2 (fun ij : Fin 3 × Fin 3 =>
    pulledRm t x (bivectorIndex3 ij.1).1 (bivectorIndex3 ij.1).2
      (bivectorIndex3 ij.2).2 (bivectorIndex3 ij.2).1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.uhlenbeckCurvatureOperatorMatrix then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.uhlenbeckCurvatureOperatorMatrix"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.uhlenbeckCurvatureOperatorMatrix ``Submission.DifferentialGeometry.PDE.RicciFlow.uhlenbeckCurvatureOperatorMatrix

noncomputable def uhlenbeckCurvatureOperatorMatrixAsMatrix
    (pulledRm : FourComp M (Fin 3)) : Real → M → Matrix (Fin 3) (Fin 3) Real :=
  fun t x i j => uhlenbeckCurvatureOperatorMatrix pulledRm t x (i, j)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.uhlenbeckCurvatureOperatorMatrixAsMatrix then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.uhlenbeckCurvatureOperatorMatrixAsMatrix"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.uhlenbeckCurvatureOperatorMatrixAsMatrix ``Submission.DifferentialGeometry.PDE.RicciFlow.uhlenbeckCurvatureOperatorMatrixAsMatrix

omit [TopologicalSpace M] in
@[simp] theorem uhlenbeckCurvatureOperatorMatrixAsMatrix_apply
    (pulledRm : FourComp M (Fin 3)) (t : Real) (x : M)
    (i j : Fin 3) :
    uhlenbeckCurvatureOperatorMatrixAsMatrix pulledRm t x i j =
      uhlenbeckCurvatureOperatorMatrix pulledRm t x (i, j) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.uhlenbeckCurvatureOperatorMatrixAsMatrix_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.uhlenbeckCurvatureOperatorMatrixAsMatrix_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.uhlenbeckCurvatureOperatorMatrixAsMatrix_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.uhlenbeckCurvatureOperatorMatrixAsMatrix_apply


omit [FiniteDimensional Real E] [CompleteSpace E] in
theorem uhlenbeckCurvatureOperatorMatrixAsMatrix_eq_curvatureOperatorMatrixAt
    {x : M} {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    {A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x}
    {pulledRm : FourComp M (Fin 3)} {t : Real}
    (hpull : ∀ a b c d : Fin 3,
      pulledRm t x a b c d =
        tensor04StandardAt (I := I) (M := M) (A : Tensor04At (I := I) (M := M) x)
          (basis a) (basis b) (basis c) (basis d)) :
    uhlenbeckCurvatureOperatorMatrixAsMatrix pulledRm t x =
      curvatureOperatorMatrixAt (I := I) x basis A := by
  ext i j
  unfold uhlenbeckCurvatureOperatorMatrixAsMatrix uhlenbeckCurvatureOperatorMatrix
    curvatureOperatorMatrixAt
  simp [hpull]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.uhlenbeckCurvatureOperatorMatrixAsMatrix_eq_curvatureOperatorMatrixAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.uhlenbeckCurvatureOperatorMatrixAsMatrix_eq_curvatureOperatorMatrixAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.uhlenbeckCurvatureOperatorMatrixAsMatrix_eq_curvatureOperatorMatrixAt ``Submission.DifferentialGeometry.PDE.RicciFlow.uhlenbeckCurvatureOperatorMatrixAsMatrix_eq_curvatureOperatorMatrixAt


omit [FiniteDimensional Real E] [CompleteSpace E] in
theorem uhlenbeckCurvatureOperatorMatrixAsMatrix_isHermitian
    {x : M} {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    {A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x}
    {pulledRm : FourComp M (Fin 3)} {t : Real}
    (hpull : ∀ a b c d : Fin 3,
      pulledRm t x a b c d =
        tensor04StandardAt (I := I) (M := M) (A : Tensor04At (I := I) (M := M) x)
          (basis a) (basis b) (basis c) (basis d)) :
    (uhlenbeckCurvatureOperatorMatrixAsMatrix pulledRm t x).IsHermitian := by
  rw [uhlenbeckCurvatureOperatorMatrixAsMatrix_eq_curvatureOperatorMatrixAt
    (I := I) (M := M) (x := x) (basis := basis) (A := A) (pulledRm := pulledRm) (t := t) hpull]
  exact curvatureOperatorMatrixAt_isHermitian (I := I) x basis A

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.uhlenbeckCurvatureOperatorMatrixAsMatrix_isHermitian then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.uhlenbeckCurvatureOperatorMatrixAsMatrix_isHermitian"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.uhlenbeckCurvatureOperatorMatrixAsMatrix_isHermitian ``Submission.DifferentialGeometry.PDE.RicciFlow.uhlenbeckCurvatureOperatorMatrixAsMatrix_isHermitian


noncomputable def uhlenbeckCurvatureOperatorReaction
    (B : FourComp M (Fin 3)) :
    Real → M → EuclideanSpace ℝ (Fin 3 × Fin 3) :=
  fun t x => WithLp.toLp 2 (fun ij : Fin 3 × Fin 3 =>
    let a := (bivectorIndex3 ij.1).1;
    let b := (bivectorIndex3 ij.1).2;
    let c := (bivectorIndex3 ij.2).2;
    let d := (bivectorIndex3 ij.2).1;
    -2 * (B t x a b c d - B t x a b d c + B t x a c b d - B t x a d b c))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.uhlenbeckCurvatureOperatorReaction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.uhlenbeckCurvatureOperatorReaction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.uhlenbeckCurvatureOperatorReaction ``Submission.DifferentialGeometry.PDE.RicciFlow.uhlenbeckCurvatureOperatorReaction

omit [CompleteSpace E] [TopologicalSpace M] in
theorem uhlenbeckCurvatureOperatorReaction_lipschitz
    (B : FourComp M (Fin 3)) (t : Real) (x : M) :
    LipschitzWith 0 (fun _ : EuclideanSpace ℝ (Fin 3 × Fin 3) =>
      uhlenbeckCurvatureOperatorReaction B t x) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro a b
  simp [uhlenbeckCurvatureOperatorReaction, dist_eq_norm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.uhlenbeckCurvatureOperatorReaction_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.uhlenbeckCurvatureOperatorReaction_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.uhlenbeckCurvatureOperatorReaction_lipschitz ``Submission.DifferentialGeometry.PDE.RicciFlow.uhlenbeckCurvatureOperatorReaction_lipschitz


omit [CompleteSpace E] in
theorem innerProductHeatReactionOn_of_uhlenbeckCurvatureOperator
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (pulledRm roughLapD B : FourComp M (Fin 3))
    (hU : UhlenbeckCurvatureEvolutionInFrameOn (D := D) pulledRm roughLapD B)
    (hlap : ∀ t : Real, t ∈ D.carrier → ∀ x : M, ∀ ij : Fin 3 × Fin 3,
      roughLapD t x (bivectorIndex3 ij.1).1 (bivectorIndex3 ij.1).2
          (bivectorIndex3 ij.2).2 (bivectorIndex3 ij.2).1 =
        laplacianAt (I := I) G t
          (fun y : M => uhlenbeckCurvatureOperatorMatrix pulledRm t y ij) x)
    (hjoint : ContinuousOn (fun q : Real × M => uhlenbeckCurvatureOperatorMatrix pulledRm q.1 q.2)
      (D.carrier ×ˢ (Set.univ : Set M)))
    (hsmooth : ∀ ij : Fin 3 × Fin 3, ∀ t : Real, t ∈ D.carrier →
      ContMDiff I 𝓘(Real, Real) ∞
        (fun x : M => uhlenbeckCurvatureOperatorMatrix pulledRm t x ij)) :
    IsInnerProductHeatReactionOn (D := D) (G := G)
      (F := EuclideanSpace ℝ (Fin 3 × Fin 3))
      (fun t x _ => uhlenbeckCurvatureOperatorReaction B t x)
      (uhlenbeckCurvatureOperatorMatrix pulledRm) := by
  refine innerProductHeatReactionOn_of_componentwise (D := D) (G := G)
    (u := uhlenbeckCurvatureOperatorMatrix pulledRm)
    (reaction := fun t x _ => uhlenbeckCurvatureOperatorReaction B t x) hjoint hsmooth ?_
  intro ij t ht x
  let a := (bivectorIndex3 ij.1).1
  let b := (bivectorIndex3 ij.1).2
  let c := (bivectorIndex3 ij.2).2
  let d := (bivectorIndex3 ij.2).1
  have hU' := hU ⟨t, ht⟩ x a b c d
  have hderivAt : HasDerivAt (fun s : Real => pulledRm s x a b c d)
      (uhlenbeckCurvatureEvolutionRHSInFrame roughLapD B (t : Real) x a b c d) (t : Real) :=
    hU'.hasDerivAt (D.regular_mem_nhds ht)
  have hrhs : uhlenbeckCurvatureEvolutionRHSInFrame roughLapD B (t : Real) x a b c d =
      laplacianAt (I := I) G (t : Real)
          (fun y : M => uhlenbeckCurvatureOperatorMatrix pulledRm (t : Real) y ij) x +
        uhlenbeckCurvatureOperatorReaction B (t : Real) x ij := by
    unfold uhlenbeckCurvatureEvolutionRHSInFrame uhlenbeckCurvatureOperatorReaction
    rw [hlap (t : Real) (D.regular_subset ht) x ij]
    ring
  have hmain := hderivAt.congr_deriv hrhs
  simpa [uhlenbeckCurvatureOperatorMatrix, a, b, c, d] using hmain

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.innerProductHeatReactionOn_of_uhlenbeckCurvatureOperator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.innerProductHeatReactionOn_of_uhlenbeckCurvatureOperator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.innerProductHeatReactionOn_of_uhlenbeckCurvatureOperator ``Submission.DifferentialGeometry.PDE.RicciFlow.innerProductHeatReactionOn_of_uhlenbeckCurvatureOperator

omit [CompleteSpace E] in
omit [TopologicalSpace M] in
theorem uhlenbeckCurvatureOperatorMatrix_eq_matrixToEuclidean
    (pulledRm : FourComp M (Fin 3)) (t : Real) (x : M) :
    uhlenbeckCurvatureOperatorMatrix pulledRm t x =
      matrixToEuclidean (uhlenbeckCurvatureOperatorMatrixAsMatrix pulledRm t x) := by
  simp [uhlenbeckCurvatureOperatorMatrix, uhlenbeckCurvatureOperatorMatrixAsMatrix,
    matrixToEuclidean]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.uhlenbeckCurvatureOperatorMatrix_eq_matrixToEuclidean then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.uhlenbeckCurvatureOperatorMatrix_eq_matrixToEuclidean"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.uhlenbeckCurvatureOperatorMatrix_eq_matrixToEuclidean ``Submission.DifferentialGeometry.PDE.RicciFlow.uhlenbeckCurvatureOperatorMatrix_eq_matrixToEuclidean

omit [TopologicalSpace M] in
theorem inner_uhlenbeckCurvatureOperatorMatrix_eq_matrix
    (ν : EuclideanSpace ℝ (Fin 3 × Fin 3))
    (pulledRm : FourComp M (Fin 3)) (t : Real) (x : M) :
    _root_.Inner.inner ℝ ν (uhlenbeckCurvatureOperatorMatrix pulledRm t x) =
      ∑ ij : Fin 3 × Fin 3,
        ν ij * uhlenbeckCurvatureOperatorMatrixAsMatrix pulledRm t x ij.1 ij.2 := by
  have hmatrix : uhlenbeckCurvatureOperatorMatrix pulledRm t x =
      matrixToEuclidean (uhlenbeckCurvatureOperatorMatrixAsMatrix pulledRm t x) := by
    ext ij
    rfl
  rw [hmatrix, inner_matrixToEuclidean]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.inner_uhlenbeckCurvatureOperatorMatrix_eq_matrix then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.inner_uhlenbeckCurvatureOperatorMatrix_eq_matrix"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.inner_uhlenbeckCurvatureOperatorMatrix_eq_matrix ``Submission.DifferentialGeometry.PDE.RicciFlow.inner_uhlenbeckCurvatureOperatorMatrix_eq_matrix

end DifferentialGeometry.PDE.RicciFlow

end
