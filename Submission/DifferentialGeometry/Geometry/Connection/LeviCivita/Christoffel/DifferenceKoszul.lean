import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Koszul.Basic
import Submission.DifferentialGeometry.Geometry.Metric.DeTurck.ConnectionDifference.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set
open scoped _root_.Manifold _root_.Topology _root_.ContDiff


namespace DifferentialGeometry
namespace Geometry
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

def metricCovDeriv (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X Y Z : Π x : M, TangentSpace I x) (x : M) : ℝ :=
  directionalDeriv (I := I) (fun b => g.inner b (Y b) (Z b)) x (X x)
    - g.inner x (cov.toFun Y x (X x)) (Z x)
    - g.inner x (Y x) (cov.toFun Z x (X x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.metricCovDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.metricCovDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.metricCovDeriv ``Submission.DifferentialGeometry.Geometry.Connection.metricCovDeriv

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem metricCovDeriv_self_eq_zero (g : SmoothRiemannianMetric I M)
    {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    metricCovDeriv (I := I) g (LeviCivita (I := I) g) X Y Z x = 0 := by
  have hmc := (LeviCivita_isMetricCompatible (I := I) g).apply hY hZ (X x)
  unfold metricCovDeriv
  rw [directionalDeriv_eq, hmc]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.metricCovDeriv_self_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.metricCovDeriv_self_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.metricCovDeriv_self_eq_zero ``Submission.DifferentialGeometry.Geometry.Connection.metricCovDeriv_self_eq_zero

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem connectionDifference_koszul (g₁ g₀ : SmoothRiemannianMetric I M)
    {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    2 * g₁.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (Y x) (X x)) (Z x) =
      metricCovDeriv (I := I) g₁ (LeviCivita (I := I) g₀) X Y Z x
      + metricCovDeriv (I := I) g₁ (LeviCivita (I := I) g₀) Y X Z x
      - metricCovDeriv (I := I) g₁ (LeviCivita (I := I) g₀) Z X Y x := by
  have hK1 := koszul_identity (I := I) (g := g₁) (LeviCivita (I := I) g₁)
    (LeviCivita_torsion_eq_zero (I := I) g₁) (LeviCivita_isMetricCompatible (I := I) g₁)
    hX hY hZ
  have hTF : ∀ ⦃A B : Π y : M, TangentSpace I y⦄ ⦃y : M⦄,
      MDiffAt (T% A) y → MDiffAt (T% B) y →
      (LeviCivita (I := I) g₀).toFun B y (A y) - (LeviCivita (I := I) g₀).toFun A y (B y)
        = VectorField.mlieBracket I A B y := fun A B y hA hB =>
    (CovariantDerivative.torsion_eq_zero_iff (LeviCivita (I := I) g₀)).mp
      (LeviCivita_torsion_eq_zero (I := I) g₀) hA hB
  have tf_XY := hTF hX hY
  have tf_XZ := hTF hX hZ
  have tf_YZ := hTF hY hZ
  set nXY := (LeviCivita (I := I) g₀).toFun Y x (X x) with hnXY
  set nYX := (LeviCivita (I := I) g₀).toFun X x (Y x) with hnYX
  set nXZ := (LeviCivita (I := I) g₀).toFun Z x (X x) with hnXZ
  set nZX := (LeviCivita (I := I) g₀).toFun X x (Z x) with hnZX
  set nYZ := (LeviCivita (I := I) g₀).toFun Z x (Y x) with hnYZ
  set nZY := (LeviCivita (I := I) g₀).toFun Y x (Z x) with hnZY
  rw [PDE.DeTurck.connectionDifference_apply (I := I) g₁ g₀ hY (X x)]
  unfold metricCovDeriv
  simp only [directionalDeriv_eq, ← hnXY, ← hnYX, ← hnXZ, ← hnZX, ← hnYZ, ← hnZY]
  simp only [directionalDeriv_eq] at hK1
  rw [← tf_XY, ← tf_XZ, ← tf_YZ] at hK1
  have hlin : ∀ a b c : TangentSpace I x,
      g₁.inner x (a - b) c = g₁.inner x a c - g₁.inner x b c := fun a b c => by
    simp [map_sub, sub_apply]
  rw [hlin, hlin, hlin] at hK1
  rw [map_sub, sub_apply, mul_sub]
  rw [hK1]
  rw [g₁.symm x (Y x) nXZ, g₁.symm x (X x) nYZ, g₁.symm x (X x) nZY]
  let dYZ : ℝ := (mfderiv I 𝓘(ℝ) (fun b => g₁.inner b (Y b) (Z b)) x) (X x)
  let dXZ : ℝ := (mfderiv I 𝓘(ℝ) (fun b => g₁.inner b (X b) (Z b)) x) (Y x)
  let dXY : ℝ := (mfderiv I 𝓘(ℝ) (fun b => g₁.inner b (X b) (Y b)) x) (Z x)
  let pXY : ℝ := g₁.inner x nXY (Z x)
  let pYX : ℝ := g₁.inner x nYX (Z x)
  let pXZ : ℝ := g₁.inner x nXZ (Y x)
  let pZX : ℝ := g₁.inner x nZX (Y x)
  let pYZ : ℝ := g₁.inner x nYZ (X x)
  let pZY : ℝ := g₁.inner x nZY (X x)
  change (dYZ + dXZ - dXY + (pXY - pYX) - (pXZ - pZX) - (pYZ - pZY)) -
      2 * pXY =
    dYZ - pXY - pXZ + (dXZ - pYX - pYZ) - (dXY - pZX - pZY)
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.connectionDifference_koszul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.connectionDifference_koszul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.connectionDifference_koszul ``Submission.DifferentialGeometry.Geometry.Connection.connectionDifference_koszul

def metricDiffCovDeriv (g₁ g₀ : SmoothRiemannianMetric I M)
    (X Y Z : Π x : M, TangentSpace I x) (x : M) : ℝ :=
  metricCovDeriv (I := I) g₁ (LeviCivita (I := I) g₀) X Y Z x
    - metricCovDeriv (I := I) g₀ (LeviCivita (I := I) g₀) X Y Z x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.metricDiffCovDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.metricDiffCovDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.metricDiffCovDeriv ``Submission.DifferentialGeometry.Geometry.Connection.metricDiffCovDeriv

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem metricDiffCovDeriv_eq_metricCovDeriv (g₁ g₀ : SmoothRiemannianMetric I M)
    {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    metricDiffCovDeriv (I := I) g₁ g₀ X Y Z x =
      metricCovDeriv (I := I) g₁ (LeviCivita (I := I) g₀) X Y Z x := by
  unfold metricDiffCovDeriv
  rw [metricCovDeriv_self_eq_zero (I := I) g₀ hY hZ, sub_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.metricDiffCovDeriv_eq_metricCovDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.metricDiffCovDeriv_eq_metricCovDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.metricDiffCovDeriv_eq_metricCovDeriv ``Submission.DifferentialGeometry.Geometry.Connection.metricDiffCovDeriv_eq_metricCovDeriv

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem connectionDifference_koszul_metricDiff (g₁ g₀ : SmoothRiemannianMetric I M)
    {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    2 * g₁.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (Y x) (X x)) (Z x) =
      metricDiffCovDeriv (I := I) g₁ g₀ X Y Z x
      + metricDiffCovDeriv (I := I) g₁ g₀ Y X Z x
      - metricDiffCovDeriv (I := I) g₁ g₀ Z X Y x := by
  rw [metricDiffCovDeriv_eq_metricCovDeriv (I := I) g₁ g₀ hY hZ,
      metricDiffCovDeriv_eq_metricCovDeriv (I := I) g₁ g₀ hX hZ,
      metricDiffCovDeriv_eq_metricCovDeriv (I := I) g₁ g₀ hX hY]
  exact connectionDifference_koszul (I := I) g₁ g₀ hX hY hZ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.connectionDifference_koszul_metricDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.connectionDifference_koszul_metricDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.connectionDifference_koszul_metricDiff ``Submission.DifferentialGeometry.Geometry.Connection.connectionDifference_koszul_metricDiff

end Connection
end Geometry
end DifferentialGeometry
