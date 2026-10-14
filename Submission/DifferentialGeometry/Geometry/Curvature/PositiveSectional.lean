import Batteries.Tactic.Alias
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Notation
import Submission.DifferentialGeometry.Geometry.Curvature.Nonnegative
import Submission.DifferentialGeometry.Geometry.Curvature.Algebraic.TensorMetric

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry

open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M]

def hasPositiveSectionalCurvature
    (g : SmoothRiemannianMetric I M) : Prop :=
  ∀ x : M, ∀ W T : TangentSpace I x,
    LinearIndependent ℝ ![W, T] →
      0 < metricRm04StandardAt (I := I) (M := M) g x W T T W

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.hasPositiveSectionalCurvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.hasPositiveSectionalCurvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.hasPositiveSectionalCurvature ``Submission.DifferentialGeometry.Geometry.hasPositiveSectionalCurvature

omit [I.Boundaryless] [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem metricRm04StandardAt_eq_zero_of_not_linearIndependent
    (g : SmoothRiemannianMetric I M) (x : M)
    (W T : TangentSpace I x) (hdep : ¬ LinearIndependent ℝ ![W, T]) :
    metricRm04StandardAt (I := I) (M := M) g x W T T W = 0 := by
  let B : TangentSpace I x → TangentSpace I x → TangentSpace I x →
      TangentSpace I x → ℝ :=
    fun X Y Z U ↦ metricRm04StandardAt (I := I) (M := M) g x X Y Z U
  have hB : IsAlgCurvForm B := by
    change IsAlgCurvForm
      (tensor04StandardAt (I := I) (M := M)
        (metricRm04At (I := I) (M := M) g x))
    exact mem_algebraicCurvatureTensorSubmodule.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (M := M) g x)
  by_cases hW : W = 0
  · subst W
    have hzero := hB.smul_left 0 (0 : TangentSpace I x) T T 0
    simpa [B] using hzero
  · rw [LinearIndependent.pair_iff' hW] at hdep
    push Not at hdep
    obtain ⟨a, rfl⟩ := hdep
    have hdiag : B W W (a • W) W = 0 := by
      have hskew := hB.anti_first W W (a • W) W
      linarith
    have hskew := hB.anti_first W (a • W) (a • W) W
    have hsmul := hB.smul_left a W W (a • W) W
    change B W (a • W) (a • W) W = 0
    rw [hskew, hsmul, hdiag]
    ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.metricRm04StandardAt_eq_zero_of_not_linearIndependent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.metricRm04StandardAt_eq_zero_of_not_linearIndependent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.metricRm04StandardAt_eq_zero_of_not_linearIndependent ``Submission.DifferentialGeometry.Geometry.metricRm04StandardAt_eq_zero_of_not_linearIndependent

omit [I.Boundaryless] [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem hasPositiveSectionalCurvature.toNonnegative
    {g : SmoothRiemannianMetric I M}
    (hsec : hasPositiveSectionalCurvature (I := I) g) :
    hasNonnegativeSectionalCurvature (I := I) g := by
  rw [hasNonnegativeSectionalCurvature_iff (I := I) g]
  intro x W T
  by_cases hlin : LinearIndependent ℝ ![W, T]
  · exact (hsec x W T hlin).le
  · rw [metricRm04StandardAt_eq_zero_of_not_linearIndependent
      (I := I) (M := M) g x W T hlin]

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Geometry.hasPositiveSectionalCurvature
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.hasPositiveSectionalCurvature.toNonnegative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.hasPositiveSectionalCurvature.toNonnegative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.hasPositiveSectionalCurvature.toNonnegative ``Submission.DifferentialGeometry.Geometry.hasPositiveSectionalCurvature.toNonnegative

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless]
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem gram_determinant_pos (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) (hvw : LinearIndependent ℝ ![v, w]) :
    0 < g.inner x v v * g.inner x w w - g.inner x v w ^ 2 := by
  have hv : v ≠ 0 := hvw.ne_zero 0
  have ha := g.pos x v hv
  let a := g.inner x v v
  let b := g.inner x v w
  have hne : a • w - b • v ≠ 0 := by
    intro hz
    have hh := hvw.eq_zero_of_pair' (sub_eq_zero.mp hz).symm
    exact ha.ne' hh.2
  have hz := g.pos x (a • w - b • v) hne
  have heq : g.inner x (a • w - b • v) (a • w - b • v) =
      a * (a * g.inner x w w - b ^ 2) := by
    simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul]
    rw [g.symm x w v]
    dsimp only [a, b]
    ring
  rw [heq] at hz
  exact pos_of_mul_pos_right hz ha.le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.gram_determinant_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.gram_determinant_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.gram_determinant_pos ``Submission.DifferentialGeometry.Geometry.gram_determinant_pos

omit [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
    [BoundarylessManifold I M] in
theorem positive_sectional_iff_quotient (g : SmoothRiemannianMetric I M) :
    hasPositiveSectionalCurvature g ↔
      ∀ x : M, ∀ v w : TangentSpace I x, LinearIndependent ℝ ![v, w] →
        0 < metricRm04StandardAt g x v w w v /
          (g.inner x v v * g.inner x w w - g.inner x v w ^ 2) := by
  constructor
  · intro hg x v w hvw
    exact div_pos (hg x v w hvw) (gram_determinant_pos g x v w hvw)
  · intro hg x v w hvw
    exact (div_pos_iff_of_pos_right (gram_determinant_pos g x v w hvw)).mp (hg x v w hvw)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.positive_sectional_iff_quotient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.positive_sectional_iff_quotient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.positive_sectional_iff_quotient ``Submission.DifferentialGeometry.Geometry.positive_sectional_iff_quotient

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless]
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem tangent_pair_linearIndependent_of_orthonormal (g : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) (hv : g.inner x v v = 1)
    (hw : g.inner x w w = 1) (hvw : g.inner x v w = 0) :
    LinearIndependent ℝ ![v, w] := by
  let : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hwv : g.inner x w v = 0 := (g.symm x w v).trans hvw
  have ho : Orthonormal ℝ ![v, w] := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j
    · exact hv
    · exact hvw
    · exact hwv
    · exact hw
  exact ho.linearIndependent

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.tangent_pair_linearIndependent_of_orthonormal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.tangent_pair_linearIndependent_of_orthonormal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.tangent_pair_linearIndependent_of_orthonormal ``Submission.DifferentialGeometry.Geometry.tangent_pair_linearIndependent_of_orthonormal

omit [SigmaCompactSpace M] in
theorem riemann_contraction_pos_of_orthonormal
    (g : SmoothRiemannianMetric I M)
    (hsec : hasPositiveSectionalCurvature (I := I) g)
    (x : M) (v w : TangentSpace I x) (hv : g.inner x v v = 1)
    (hw : g.inner x w w = 1) (hvw : g.inner x v w = 0) :
    0 < g.inner x (riemannOp (LeviCivita (I := I) g) x v w w) v := by
  have hpos := hsec x v w (tangent_pair_linearIndependent_of_orthonormal g x v w hv hw hvw)
  rw [rm04_eq_inner_riem, g.symm] at hpos
  exact hpos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemann_contraction_pos_of_orthonormal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemann_contraction_pos_of_orthonormal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemann_contraction_pos_of_orthonormal ``Submission.DifferentialGeometry.Geometry.riemann_contraction_pos_of_orthonormal

end DifferentialGeometry.Geometry

namespace DifferentialGeometry.Geometry

@[reducible] alias HasPositiveSectionalCurvature := DifferentialGeometry.Geometry.hasPositiveSectionalCurvature
end DifferentialGeometry.Geometry

namespace DifferentialGeometry.Geometry.HasPositiveSectionalCurvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M]

omit [I.Boundaryless] [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem toNonnegative {g : DifferentialGeometry.SmoothRiemannianMetric I M}
    (hsec : DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I) g) :
    DifferentialGeometry.Geometry.HasNonnegativeSectionalCurvature (I := I) g :=
  DifferentialGeometry.Geometry.hasPositiveSectionalCurvature.toNonnegative hsec

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.HasPositiveSectionalCurvature.toNonnegative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.HasPositiveSectionalCurvature.toNonnegative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.HasPositiveSectionalCurvature.toNonnegative ``Submission.DifferentialGeometry.Geometry.HasPositiveSectionalCurvature.toNonnegative

end DifferentialGeometry.Geometry.HasPositiveSectionalCurvature
