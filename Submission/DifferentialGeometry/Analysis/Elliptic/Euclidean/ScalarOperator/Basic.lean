import Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.Duhamel.FrozenPositiveDefinite
import Submission.DifferentialGeometry.Analysis.Calculus.SecondDerivative.Minimum
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.Ring

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

open scoped _root_.Topology

noncomputable section

namespace DifferentialGeometry.Analysis

private theorem fderiv_fderiv_fun_mul_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => f y * g y)) x v w =
      f x * fderiv ℝ (fderiv ℝ g) x v w +
        g x * fderiv ℝ (fderiv ℝ f) x v w +
        fderiv ℝ f x v * fderiv ℝ g x w +
        fderiv ℝ f x w * fderiv ℝ g x v := by
  have hfd := hf.differentiableAt (by norm_num)
  have hgd := hg.differentiableAt (by norm_num)
  have hfdd := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hgdd := (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hnear : fderiv ℝ (fun y => f y * g y) =ᶠ[𝓝 x]
      (fun y => f y • fderiv ℝ g y + g y • fderiv ℝ f y) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hfy hgy
    exact fderiv_fun_mul (hfy.differentiableAt (by norm_num))
      (hgy.differentiableAt (by norm_num))
  rw [hnear.fderiv_eq]
  erw [fderiv_fun_add (hfd.smul hgdd) (hgd.smul hfdd),
    fderiv_fun_smul hfd hgdd, fderiv_fun_smul hgd hfdd]
  simp only [_root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.fderiv_fderiv_fun_mul_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.fderiv_fderiv_fun_mul_apply target :: scope.openDecls } }


variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "V" => EuclideanSpace ℝ ι

def scalarEllipticOperator (A : V → Matrix ι ι ℝ) (b : V → ι → ℝ)
    (u : V → ℝ) (x : V) : ℝ :=
  (∑ i, ∑ j, A x i j * fderiv ℝ (fderiv ℝ u) x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) +
    ∑ i, b x i * fderiv ℝ u x (EuclideanSpace.single i 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.scalarEllipticOperator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.scalarEllipticOperator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.scalarEllipticOperator ``Submission.DifferentialGeometry.Analysis.scalarEllipticOperator


theorem scalarEllipticOperator_mul
    (A : V → Matrix ι ι ℝ) (b : V → ι → ℝ) {f g : V → ℝ} {x : V}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    scalarEllipticOperator A b (fun y => f y * g y) x =
      f x * scalarEllipticOperator A b g x + g x * scalarEllipticOperator A b f x +
        ∑ i, ∑ j, A x i j *
          (fderiv ℝ f x (EuclideanSpace.single i 1) * fderiv ℝ g x (EuclideanSpace.single j 1) +
            fderiv ℝ f x (EuclideanSpace.single j 1) * fderiv ℝ g x
              (EuclideanSpace.single i 1)) := by
  have hprincipal (i j : ι) : A x i j *
      fderiv ℝ (fderiv ℝ (fun y => f y * g y)) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
      f x * (A x i j * fderiv ℝ (fderiv ℝ g) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) +
      g x * (A x i j * fderiv ℝ (fderiv ℝ f) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) +
      A x i j *
        (fderiv ℝ f x (EuclideanSpace.single i 1) * fderiv ℝ g x (EuclideanSpace.single j 1) +
          fderiv ℝ f x (EuclideanSpace.single j 1) * fderiv ℝ g x (EuclideanSpace.single i 1)) := by
    rw [fderiv_fderiv_fun_mul_apply hf hg]
    ring
  have hdrift (i : ι) : b x i *
      fderiv ℝ (fun y => f y * g y) x (EuclideanSpace.single i 1) =
      f x * (b x i * fderiv ℝ g x (EuclideanSpace.single i 1)) +
        g x * (b x i * fderiv ℝ f x (EuclideanSpace.single i 1)) := by
    rw [fderiv_fun_mul (hf.differentiableAt (by norm_num)) (hg.differentiableAt (by norm_num))]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  unfold scalarEllipticOperator
  simp_rw [hprincipal, hdrift]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.scalarEllipticOperator_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.scalarEllipticOperator_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.scalarEllipticOperator_mul ``Submission.DifferentialGeometry.Analysis.scalarEllipticOperator_mul

theorem scalarEllipticOperator_mul_of_isSymm
    (A : V → Matrix ι ι ℝ) (b : V → ι → ℝ) {f g : V → ℝ} {x : V}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) (hA : (A x).IsSymm) :
    scalarEllipticOperator A b (fun y => f y * g y) x =
      f x * scalarEllipticOperator A b g x + g x * scalarEllipticOperator A b f x +
        2 * ∑ i, ∑ j, A x i j *
          fderiv ℝ f x (EuclideanSpace.single i 1) * fderiv ℝ g x (EuclideanSpace.single j 1) := by
  rw [scalarEllipticOperator_mul A b hf hg]
  have hswap : (∑ i, ∑ j, A x i j *
      fderiv ℝ f x (EuclideanSpace.single j 1) * fderiv ℝ g x (EuclideanSpace.single i 1)) =
      ∑ i, ∑ j, A x i j *
        fderiv ℝ f x (EuclideanSpace.single i 1) * fderiv ℝ g x (EuclideanSpace.single j 1) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hA.apply i j]
  simp only [mul_add, ← mul_assoc, Finset.sum_add_distrib]
  rw [hswap]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.scalarEllipticOperator_mul_of_isSymm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.scalarEllipticOperator_mul_of_isSymm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.scalarEllipticOperator_mul_of_isSymm ``Submission.DifferentialGeometry.Analysis.scalarEllipticOperator_mul_of_isSymm

theorem scalarEllipticOperator_sq
    (A : V → Matrix ι ι ℝ) (b : V → ι → ℝ) {u : V → ℝ} {x : V}
    (hu : ContDiffAt ℝ 2 u x) :
    scalarEllipticOperator A b (fun y => u y ^ 2) x =
      2 * u x * scalarEllipticOperator A b u x +
        2 * ∑ i, ∑ j, A x i j *
          fderiv ℝ u x (EuclideanSpace.single i 1) * fderiv ℝ u x (EuclideanSpace.single j 1) := by
  simp_rw [pow_two]
  rw [scalarEllipticOperator_mul A b hu hu]
  have hc (i j : ι) : A x i j *
      (fderiv ℝ u x (EuclideanSpace.single i 1) * fderiv ℝ u x (EuclideanSpace.single j 1) +
        fderiv ℝ u x (EuclideanSpace.single j 1) * fderiv ℝ u x (EuclideanSpace.single i 1)) =
      2 * (A x i j * fderiv ℝ u x (EuclideanSpace.single i 1) *
        fderiv ℝ u x (EuclideanSpace.single j 1)) := by ring
  simp_rw [hc, ← Finset.mul_sum]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.scalarEllipticOperator_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.scalarEllipticOperator_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.scalarEllipticOperator_sq ``Submission.DifferentialGeometry.Analysis.scalarEllipticOperator_sq

theorem scalarEllipticOperator_nonpos_of_isLocalMax
    (A : V → Matrix ι ι ℝ) (b : V → ι → ℝ) {u : V → ℝ} {x : V}
    (hu : ContDiffAt ℝ 2 u x) (hmax : IsLocalMax u x) (hA : (A x).PosDef) :
    scalarEllipticOperator A b u x ≤ 0 := by
  have hH (v : V) : fderiv ℝ (fderiv ℝ u) x v v ≤ 0 := by
    have hn := secondDirectional_nonneg_of_localMin hu.neg hmax.neg v
    simp only [fderiv_fun_neg, neg_apply, neg_nonneg] at hn
    have hd := (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have he : fderiv ℝ (fun q => fderiv ℝ u q v) x v =
        fderiv ℝ (fderiv ℝ u) x v v := by
      rw [fderiv_clm_apply hd (differentiableAt_const v)]
      simp
    rwa [he] at hn
  have hprincipal : Parabolic.Euclidean.matrixLap (A x) (fderiv ℝ (fderiv ℝ u) x) ≤ 0 := by
    rw [← Parabolic.Euclidean.spd_factorLap (A x) hA,
      Parabolic.Euclidean.factorLap]
    exact Finset.sum_nonpos fun i _ => hH _
  simpa only [scalarEllipticOperator, hmax.fderiv_eq_zero, zero_apply,
    _root_.MulZeroClass.mul_zero, Finset.sum_const_zero, add_zero, Parabolic.Euclidean.matrixLap,
    EuclideanSpace.basisFun_apply, smul_eq_mul] using hprincipal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.scalarEllipticOperator_nonpos_of_isLocalMax then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.scalarEllipticOperator_nonpos_of_isLocalMax"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.scalarEllipticOperator_nonpos_of_isLocalMax ``Submission.DifferentialGeometry.Analysis.scalarEllipticOperator_nonpos_of_isLocalMax

@[simp]
theorem scalarEllipticOperator_const
    (A : V → Matrix ι ι ℝ) (b : V → ι → ℝ) (c : ℝ) (x : V) :
    scalarEllipticOperator A b (fun _ => c) x = 0 := by
  simp [scalarEllipticOperator]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.scalarEllipticOperator_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.scalarEllipticOperator_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.scalarEllipticOperator_const ``Submission.DifferentialGeometry.Analysis.scalarEllipticOperator_const

theorem scalarEllipticOperator_const_mul
    (A : V → Matrix ι ι ℝ) (b : V → ι → ℝ) {u : V → ℝ} {x : V}
    (hu : ContDiffAt ℝ 2 u x) (c : ℝ) :
    scalarEllipticOperator A b (fun y => c * u y) x = c * scalarEllipticOperator A b u x := by
  simpa only [scalarEllipticOperator_const, fderiv_const,
    fderiv_const_apply, zero_apply, _root_.MulZeroClass.zero_mul, _root_.MulZeroClass.mul_zero,
    add_zero, zero_add, Finset.sum_const_zero] using
      scalarEllipticOperator_mul A b (f := fun _ => c) contDiffAt_const hu

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.scalarEllipticOperator_const_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.scalarEllipticOperator_const_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.scalarEllipticOperator_const_mul ``Submission.DifferentialGeometry.Analysis.scalarEllipticOperator_const_mul

theorem scalarEllipticOperator_add
    (A : V → Matrix ι ι ℝ) (b : V → ι → ℝ) {f g : V → ℝ} {x : V}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    scalarEllipticOperator A b (fun y => f y + g y) x =
      scalarEllipticOperator A b f x + scalarEllipticOperator A b g x := by
  have hnear : fderiv ℝ (fun y => f y + g y) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ f y + fderiv ℝ g y) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hfy hgy
    exact fderiv_fun_add (hfy.differentiableAt (by norm_num))
      (hgy.differentiableAt (by norm_num))
  have hH : fderiv ℝ (fderiv ℝ (fun y => f y + g y)) x =
      fderiv ℝ (fderiv ℝ f) x + fderiv ℝ (fderiv ℝ g) x := by
    rw [hnear.fderiv_eq]
    exact fderiv_fun_add
      ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
      ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
  unfold scalarEllipticOperator
  rw [hH, fderiv_fun_add (hf.differentiableAt (by norm_num))
    (hg.differentiableAt (by norm_num))]
  simp only [add_apply, mul_add, Finset.sum_add_distrib]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.scalarEllipticOperator_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.scalarEllipticOperator_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.scalarEllipticOperator_add ``Submission.DifferentialGeometry.Analysis.scalarEllipticOperator_add

theorem scalarEllipticOperator_sum {κ : Type*}
    (A : V → Matrix ι ι ℝ) (b : V → ι → ℝ) (s : Finset κ)
    (f : κ → V → ℝ) {x : V} (hf : ∀ k ∈ s, ContDiffAt ℝ 2 (f k) x) :
    scalarEllipticOperator A b (fun y => ∑ k ∈ s, f k y) x =
      ∑ k ∈ s, scalarEllipticOperator A b (f k) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hks ih =>
      simp only [Finset.sum_insert hks]
      rw [scalarEllipticOperator_add A b (hf k (Finset.mem_insert_self k s))
        (ContDiffAt.sum fun j hj => hf j (Finset.mem_insert_of_mem hj))]
      rw [ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.scalarEllipticOperator_sum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.scalarEllipticOperator_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.scalarEllipticOperator_sum ``Submission.DifferentialGeometry.Analysis.scalarEllipticOperator_sum


end DifferentialGeometry.Analysis

end

end
