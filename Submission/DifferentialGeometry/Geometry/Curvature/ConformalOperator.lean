import Submission.DifferentialGeometry.Geometry.Curvature.TraceNormalizedOperator
import Submission.DifferentialGeometry.Geometry.Curvature.Conformal
import Submission.DifferentialGeometry.Geometry.Operator.OrthonormalTrace
import Submission.DifferentialGeometry.Geometry.Metric.Conformal.OfContDiff

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Connection _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.Submission.DifferentialGeometry.Geometry.Metric _root_.Submission.DifferentialGeometry.Geometry.Operator
open scoped _root_.Manifold _root_.ContDiff _root_.InnerProductSpace _root_.BigOperators
namespace DifferentialGeometry.Geometry.Curvature

private def kulkarni {V : Type*} (G S : V → V → ℝ) (u v w z : V) : ℝ :=
  S v w * G u z + S u z * G v w - S u w * G v z - S v z * G u w

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.kulkarni
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.kulkarni target :: scope.openDecls } }

private theorem kulkarni_isAlg {V : Type*} [AddCommGroup V] [Module ℝ V]
    (G S : V → V → ℝ)
    (hGa : ∀ u v w, G (u + v) w = G u w + G v w)
    (hGs : ∀ (a : ℝ) u v, G (a • u) v = a * G u v)
    (hGsym : ∀ u v, G u v = G v u)
    (hSa : ∀ u v w, S (u + v) w = S u w + S v w)
    (hSs : ∀ (a : ℝ) u v, S (a • u) v = a * S u v)
    (hSsym : ∀ u v, S u v = S v u) : IsAlgCurvForm (kulkarni G S) where
  add_left := by intros; simp only [kulkarni, hGa, hSa]; ring
  smul_left := by intros; simp only [kulkarni, hGs, hSs]; ring
  anti_first := by intros; simp only [kulkarni]; ring
  anti_last := by intros; simp only [kulkarni]; ring
  bianchi := by
    intro u v w z
    simp only [kulkarni]
    rw [hGsym w v, hGsym w u, hGsym v u, hSsym w v, hSsym w u, hSsym v u]
    ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.kulkarni_isAlg
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.kulkarni_isAlg target :: scope.openDecls } }

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [I.Boundaryless] [BoundarylessManifold I M]
private local instance _root_.Submission.DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry target :: scope.openDecls } }
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.E3 target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [T2Space M] [I.Boundaryless] [BoundarylessManifold I M] in
def conformalBasisAt (F : M → ℝ) (x : M)
    (B : Module.Basis (Fin 3) ℝ (TangentSpace I x)) : Module.Basis (Fin 3) ℝ (TangentSpace I x) :=
  B.map (LinearEquiv.smulOfNeZero ℝ (TangentSpace I x) (Real.exp (-F x)) (Real.exp_ne_zero _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.conformalBasisAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.conformalBasisAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.conformalBasisAt ``Submission.DifferentialGeometry.Geometry.Curvature.conformalBasisAt

omit [FiniteDimensional ℝ E] [T2Space M] [I.Boundaryless] [BoundarylessManifold I M]
  [IsManifold I ∞ M] in
theorem conformalBasisAt_apply (F : M → ℝ) (x : M)
    (B : Module.Basis (Fin 3) ℝ (TangentSpace I x)) (i : Fin 3) :
    conformalBasisAt F x B i = Real.exp (-F x) • B i := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.conformalBasisAt_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.conformalBasisAt_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.conformalBasisAt_apply ``Submission.DifferentialGeometry.Geometry.Curvature.conformalBasisAt_apply

omit [FiniteDimensional ℝ E] [T2Space M] [I.Boundaryless] [BoundarylessManifold I M] in
def bivectorNormalAt (x : M) (B : Module.Basis (Fin 3) ℝ (TangentSpace I x)) (c : E3) :
    TangentSpace I x := c 2 • B 0 - c 1 • B 1 + c 0 • B 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.bivectorNormalAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.bivectorNormalAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.bivectorNormalAt ``Submission.DifferentialGeometry.Geometry.Curvature.bivectorNormalAt

private theorem exp_normalization (r : ℝ) : Real.exp (2 * r) * Real.exp (-r) ^ 2 = 1 := by
  rw [pow_two, ← Real.exp_add, ← Real.exp_add]
  convert Real.exp_zero using 2
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.exp_normalization
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.exp_normalization target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [T2Space M] [I.Boundaryless] [BoundarylessManifold I M] in
theorem conformalBasisAt_orthonormal (g : SmoothRiemannianMetric I M)
    (F : M → ℝ) (hF : ContMDiff I 𝓘(ℝ) ∞ F) (x : M)
    (B : Module.Basis (Fin 3) ℝ (TangentSpace I x)) (hB : OrthonormalBasisAt g x B) :
    OrthonormalBasisAt (conformalMetricOfContDiff g F hF) x (conformalBasisAt F x B) := by
  have hBij : ∀ i j, g.inner x (B i) (B j) = delta3 i j := hB
  intro i j
  rw [conformalBasisAt_apply, conformalBasisAt_apply, conformalMetricOfContDiff_inner]
  simp only [map_smul, smul_apply, smul_eq_mul, hBij]
  have he := exp_normalization (F x)
  by_cases hij : i = j
  · simp only [hij, delta3, ↓reduceIte, mul_one]
    nlinarith [he]
  · simp only [delta3, hij, ↓reduceIte, _root_.MulZeroClass.mul_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.conformalBasisAt_orthonormal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.conformalBasisAt_orthonormal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.conformalBasisAt_orthonormal ``Submission.DifferentialGeometry.Geometry.Curvature.conformalBasisAt_orthonormal

omit [FiniteDimensional ℝ E] [T2Space M] [I.Boundaryless] [BoundarylessManifold I M] in
theorem bivectorNormalAt_inner_self (g : SmoothRiemannianMetric I M) (x : M)
    (B : Module.Basis (Fin 3) ℝ (TangentSpace I x)) (hB : OrthonormalBasisAt g x B) (c : E3) :
    g.inner x (bivectorNormalAt x B c) (bivectorNormalAt x B c) = ‖c‖ ^ 2 := by
  have hBij : ∀ i j, g.inner x (B i) (B j) = delta3 i j := hB
  simp only [bivectorNormalAt, map_add, map_sub, map_smul, add_apply, sub_apply, smul_apply,
    smul_eq_mul, hBij, delta3, Fin.isValue, Fin.reduceEq, ↓reduceIte]
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.bivectorNormalAt_inner_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.bivectorNormalAt_inner_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.bivectorNormalAt_inner_self ``Submission.DifferentialGeometry.Geometry.Curvature.bivectorNormalAt_inner_self

private def conformalCorrection (g : SmoothRiemannianMetric I M) (F : M → ℝ) (x : M)
    (u v : TangentSpace I x) : ℝ :=
  -hessFun g F x u v + mvfderiv I F x u * mvfderiv I F x v -
    (g.inner x (gradFun g F x) (gradFun g F x) / 2) * g.inner x u v

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.conformalCorrection
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.conformalCorrection target :: scope.openDecls } }

private theorem full_conformal_curvature (g : SmoothRiemannianMetric I M)
    (F : M → ℝ) (hF : ContMDiff I 𝓘(ℝ) ∞ F) (x : M) (u v w z : TangentSpace I x) :
    metricRm04StandardAt (conformalMetricOfContDiff g F hF) x u v w z = Real.exp (2 * F x) *
      (metricRm04StandardAt g x u v w z + kulkarni (fun a b => g.inner x a b) (conformalCorrection g F x) u v w z) := by
  let G := fun a b : TangentSpace I x => g.inner x a b
  let S := conformalCorrection g F x
  have hK : IsAlgCurvForm (kulkarni G S) := by
    apply kulkarni_isAlg
    · intro a b c; simp only [G, map_add, add_apply]
    · intro a b c; simp only [G, map_smul, smul_apply, smul_eq_mul]
    · exact g.symm x
    · intro a b c; simp only [S, conformalCorrection, map_add, add_apply, LinearMap.add_apply]; ring
    · intro a b c; simp only [S, conformalCorrection, map_smul, smul_apply, LinearMap.smul_apply, smul_eq_mul]; ring
    · intro a b
      dsimp only [S, conformalCorrection]
      rw [hessFun_symm_of_boundaryless g hF x a b, g.symm x a b]
      ring
  have hR : IsAlgCurvForm (metricRm04StandardAt g x) :=
    mem_algebraicCurvatureTensorSubmodule.mp (metricRm04At_mem_algebraicCurvatureTensorSubmodule g x)
  have hR' : IsAlgCurvForm (metricRm04StandardAt (conformalMetricOfContDiff g F hF) x) :=
    mem_algebraicCurvatureTensorSubmodule.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule (conformalMetricOfContDiff g F hF) x)
  have heq := hR'.ext ((hR.add hK).smul (Real.exp (2 * F x))) (by
    intro a b
    rw [hR'.anti_last a b a b, metricRm04StdAt_conformalMetric_plane]
    rw [hR.anti_last a b a b]
    simp only [kulkarni, S, G, conformalCorrection]
    rw [hessFun_symm_of_boundaryless g hF x b a, g.symm x b a]
    ring)
  exact heq u v w z

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.full_conformal_curvature
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.full_conformal_curvature target :: scope.openDecls } }

private theorem curvature_smul_four (g : SmoothRiemannianMetric I M) (x : M)
    (t : ℝ) (u v w z : TangentSpace I x) :
    metricRm04StandardAt g x (t • u) (t • v) (t • w) (t • z) =
      t ^ 4 * metricRm04StandardAt g x u v w z := by
  let : NormedAddCommGroup (TangentSpace I x →L[ℝ] TangentSpace I x) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (TangentSpace I x →L[ℝ] TangentSpace I x) :=
    ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x) :=
    ContinuousLinearMap.toNormedSpace
  rw [rm04_eq_inner_riem, rm04_eq_inner_riem]
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.curvature_smul_four
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.curvature_smul_four target :: scope.openDecls } }

omit [BoundarylessManifold I M] in
private theorem correction_contraction (g : SmoothRiemannianMetric I M)
    (F : M → ℝ) (hF : ContMDiff I 𝓘(ℝ) ∞ F) (x : M)
    (B : Module.Basis (Fin 3) ℝ (TangentSpace I x)) (hB : OrthonormalBasisAt g x B) (c : E3) :
    (∑ i : Fin 3, ∑ j : Fin 3, c i * c j *
      kulkarni (fun a b => g.inner x a b) (conformalCorrection g F x)
        (B (bivectorIndex3 i).1) (B (bivectorIndex3 i).2)
        (B (bivectorIndex3 j).2) (B (bivectorIndex3 j).1)) =
      hessFun g F x (bivectorNormalAt x B c) (bivectorNormalAt x B c) -
        laplacian (LeviCivita g) g F x * ‖c‖ ^ 2 -
        (mvfderiv I F x (bivectorNormalAt x B c)) ^ 2 := by
  have hBij : ∀ i j, g.inner x (B i) (B j) = delta3 i j := hB
  have hBon : ∀ i j, g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0 := hB
  rw [laplacian_eq_sum_hessFun g F hF x B hBon]
  simp only [Fin.sum_univ_three, bivectorIndex3, Fin.isValue, Fin.reduceEq, ↓reduceIte,
    kulkarni, conformalCorrection, hBij, delta3]
  rw [inner_gradFun_self_eq_sum_sq g F x B hBon, EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_three, bivectorNormalAt, map_add, map_sub, map_smul,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [hessFun_symm_of_boundaryless g hF x (B 1) (B 0),
    hessFun_symm_of_boundaryless g hF x (B 2) (B 0),
    hessFun_symm_of_boundaryless g hF x (B 2) (B 1)]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.correction_contraction
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.correction_contraction target :: scope.openDecls } }

private theorem exp_four_normalization (r : ℝ) :
    Real.exp (-r) ^ 4 * Real.exp (2 * r) = Real.exp (-(2 * r)) := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.exp_four_normalization
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.exp_four_normalization target :: scope.openDecls } }

theorem traceNormalizedCurvatureOperatorAt_conformal_inner_self
    (g : SmoothRiemannianMetric I M) (F : M → ℝ) (hF : ContMDiff I 𝓘(ℝ) ∞ F)
    (x : M) (B : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (hB : OrthonormalBasisAt g x B) (c : E3) :
    ⟪traceNormalizedCurvatureOperatorAt (conformalMetricOfContDiff g F hF) x
        (conformalBasisAt F x B) c, c⟫_ℝ =
      Real.exp (-(2 * F x)) * (⟪traceNormalizedCurvatureOperatorAt g x B c, c⟫_ℝ +
        2 * (hessFun g F x (bivectorNormalAt x B c) (bivectorNormalAt x B c) -
          laplacian (LeviCivita g) g F x * ‖c‖ ^ 2 -
          (mvfderiv I F x (bivectorNormalAt x B c)) ^ 2)) := by
  let R := fun i j : Fin 3 => metricRm04StandardAt g x
    (B (bivectorIndex3 i).1) (B (bivectorIndex3 i).2)
    (B (bivectorIndex3 j).2) (B (bivectorIndex3 j).1)
  let K := fun i j : Fin 3 =>
    kulkarni (fun a b => g.inner x a b) (conformalCorrection g F x)
      (B (bivectorIndex3 i).1) (B (bivectorIndex3 i).2)
      (B (bivectorIndex3 j).2) (B (bivectorIndex3 j).1)
  have hentry (i j : Fin 3) : metricRm04StandardAt (conformalMetricOfContDiff g F hF) x
      (conformalBasisAt F x B (bivectorIndex3 i).1)
      (conformalBasisAt F x B (bivectorIndex3 i).2)
      (conformalBasisAt F x B (bivectorIndex3 j).2)
      (conformalBasisAt F x B (bivectorIndex3 j).1) =
      Real.exp (-(2 * F x)) * (R i j + K i j) := by
    simp only [conformalBasisAt_apply]
    rw [curvature_smul_four, full_conformal_curvature, ← mul_assoc, exp_four_normalization]
  rw [traceNormalizedCurvatureOperatorAt_inner_self,
    traceNormalizedCurvatureOperatorAt_inner_self]
  simp_rw [hentry]
  have hsum : (∑ i : Fin 3, ∑ j : Fin 3,
      c i * c j * (Real.exp (-(2 * F x)) * (R i j + K i j))) =
      Real.exp (-(2 * F x)) *
        ((∑ i : Fin 3, ∑ j : Fin 3, c i * c j * R i j) +
         (∑ i : Fin 3, ∑ j : Fin 3, c i * c j * K i j)) := by
    calc
      _ = ∑ i : Fin 3, ∑ j : Fin 3, Real.exp (-(2 * F x)) *
          (c i * c j * R i j + c i * c j * K i j) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  rw [hsum]
  have hK := correction_contraction g F hF x B hB c
  change (∑ i : Fin 3, ∑ j : Fin 3, c i * c j * K i j) = _ at hK
  rw [hK]
  dsimp only [R]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.traceNormalizedCurvatureOperatorAt_conformal_inner_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.traceNormalizedCurvatureOperatorAt_conformal_inner_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.traceNormalizedCurvatureOperatorAt_conformal_inner_self ``Submission.DifferentialGeometry.Geometry.Curvature.traceNormalizedCurvatureOperatorAt_conformal_inner_self

end DifferentialGeometry.Geometry.Curvature
