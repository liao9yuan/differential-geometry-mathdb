import Submission.DifferentialGeometry.Geometry.Connection.Laplacian.VectorBundle

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open scoped _root_.Manifold _root_.ContDiff

namespace CovariantDerivative
open _root_.CovariantDerivative

open _root_.CovariantDerivative in
theorem rawBundleConnLap_map
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {V : M → Type*} [TopologicalSpace (_root_.Bundle.TotalSpace F V)]
    [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
    [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
    [∀ x, ContinuousSMul ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {W : M → Type*} [TopologicalSpace (_root_.Bundle.TotalSpace G W)]
    [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)]
    [∀ x, TopologicalSpace (W x)] [∀ x, IsTopologicalAddGroup (W x)]
    [∀ x, ContinuousSMul ℝ (W x)] [FiberBundle G W]
    (D : CovariantDerivative I F V) (hD : _root_.CovariantDerivative.ContMDiffCovariantDerivative D ∞)
    (C : CovariantDerivative I G W) (φ : ∀ x, V x →ₗ[ℝ] W x)
    (hmap : ∀ (S : ∀ x, V x),
      ContMDiff I (I.prod 𝓘(ℝ, F)) 1 (fun x => TotalSpace.mk' F x (S x)) →
      ∀ (x : M) (X : TangentSpace I x),
        C (fun y => φ y (S y)) x X = φ x (D S x X))
    (g : SmoothRiemannianMetric I M) (R : ∀ x, V x)
    (hR : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun x => TotalSpace.mk' F x (R x)))
    (x : M) : rawBundleConnLap g C (fun y => φ y (R y)) x =
      φ x (rawBundleConnLap g D R x) := by
  unfold rawBundleConnLap
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  let _ : NeZero (Module.finrank ℝ E) :=
    ⟨Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩
  let Z := smoothOrthoFrame g x i
  have hZ := smoothOrthoFrame_smooth g x i
  have hDZ : ContMDiff I (I.prod 𝓘(ℝ, F)) 1
      (fun y => TotalSpace.mk' F y (D R y (Z y))) := by
    intro y
    exact (hD.contMDiffAt (m := 1) (hR y) (by norm_num)).clm_bundle_apply
      (hZ.contMDiffAt.of_le (by simp))
  have hfirst : (fun y => C (fun z => φ z (R z)) y (Z y)) =
      (fun y => φ y (D R y (Z y))) := by
    funext y
    exact hmap R (hR.of_le (by norm_num)) y (Z y)
  change C (fun y => C (fun z => φ z (R z)) y (Z y)) x (Z x) -
      C (fun z => φ z (R z)) x (LeviCivita g Z x (Z x)) = _
  rw [hfirst, hmap _ hDZ, hmap R (hR.of_le (by norm_num)), map_sub]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.rawBundleConnLap_map then
    throwError "Refusing to shadow existing declaration CovariantDerivative.rawBundleConnLap_map"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.rawBundleConnLap_map ``Submission.CovariantDerivative.rawBundleConnLap_map

end CovariantDerivative

namespace DifferentialGeometry.Geometry.Connection

theorem rawBundleConnLap_const_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {V : M → Type*} [TopologicalSpace (_root_.Bundle.TotalSpace F V)]
    [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
    [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
    [∀ x, ContinuousSMul ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
    (g : SmoothRiemannianMetric I M)
    (D : CovariantDerivative I F V) (hD : CovariantDerivative.ContMDiffCovariantDerivative D ∞)
    (R : ∀ x, V x)
    (hR : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun x => TotalSpace.mk' F x (R x)))
    (a : ℝ) (x : M) : rawBundleConnLap g D (fun y => a • R y) x =
      a • rawBundleConnLap g D R x := by
  let φ : ∀ y, V y →ₗ[ℝ] V y := fun _ => a • LinearMap.id
  have hmap (S : ∀ y, V y)
      (hS : ContMDiff I (I.prod 𝓘(ℝ, F)) 1 (fun y => TotalSpace.mk' F y (S y)))
      (y : M) (X : TangentSpace I y) : D (fun z => φ z (S z)) y X = φ y (D S y X) := by
    change D (fun z => a • S z) y X = a • D S y X
    exact congrArg (fun L => L X) (D.isCovariantDerivativeOnUniv.smul_const a
      ((hS y).mdifferentiableAt one_ne_zero))
  exact CovariantDerivative.rawBundleConnLap_map (F := F) (V := V) (G := F) (W := V)
    D hD D φ hmap g R hR x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.rawBundleConnLap_const_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.rawBundleConnLap_const_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.rawBundleConnLap_const_smul ``Submission.DifferentialGeometry.Geometry.Connection.rawBundleConnLap_const_smul

end DifferentialGeometry.Geometry.Connection
