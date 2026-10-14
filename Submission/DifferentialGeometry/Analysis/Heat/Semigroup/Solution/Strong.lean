import Submission.DifferentialGeometry.Analysis.Calculus.Derivative.HilbertBasis
import Submission.DifferentialGeometry.Analysis.Heat.Semigroup.Solution.MildEquation
import Submission.DifferentialGeometry.Analysis.Heat.Smoothing.Regularity.ClosedManifold
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace HeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian

private local instance _root_.Submission.DifferentialGeometry.Analysis.HeatEquation.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.HeatEquation.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.HeatEquation.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.HeatEquation.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.HeatEquation.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.HeatEquation.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.HeatEquation.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.HeatEquation.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.HeatEquation.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.HeatEquation.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.HeatEquation.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.HeatEquation.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

def IsStrongSolutionAt
    (g : SmoothRiemannianMetric I M)
    (u f : ℝ → _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (t : ℝ) : Prop :=
  ∃ u_h : laplacianDomain (I := I) (M := M) g,
    H1ComplToLp (I := I) (M := M) g (u_h : H1Compl g) = u t ∧
      HasDerivAt u (laplacianOp (I := I) (M := M) g u_h + f t) t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.IsStrongSolutionAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.IsStrongSolutionAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.IsStrongSolutionAt ``Submission.DifferentialGeometry.Analysis.HeatEquation.IsStrongSolutionAt

def IsStrongSolutionOn
    (g : SmoothRiemannianMetric I M)
    (u f : ℝ → _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (s : Set ℝ) : Prop :=
  ∀ t ∈ s, IsStrongSolutionAt (I := I) (M := M) g u f t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.IsStrongSolutionOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.IsStrongSolutionOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.IsStrongSolutionOn ``Submission.DifferentialGeometry.Analysis.HeatEquation.IsStrongSolutionOn

theorem mildSolution_hasDerivAt_laplacianOp_add_of_lift
    (g : SmoothRiemannianMetric I M)
    (u_0 : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {f : ℝ → _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hf : Continuous f) {t : ℝ} (ht : 0 < t)
    {v : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hderiv : HasDerivAt (mildSolution (I := I) (M := M) g u_0 f) v t)
    (u_h : laplacianDomain (I := I) (M := M) g)
    (hu_h : H1ComplToLp (I := I) (M := M) g (u_h : H1Compl g) =
      mildSolution (I := I) (M := M) g u_0 f t) :
    HasDerivAt (mildSolution (I := I) (M := M) g u_0 f)
      (laplacianOp (I := I) (M := M) g u_h + f t) t := by
  have hv : v = laplacianOp (I := I) (M := M) g u_h + f t := by
    set b := resolventHilbertEigenbasisSigma (I := I) (M := M) g
    apply b.repr.injective
    ext i
    have hinner : HasDerivAt
        (fun s : ℝ => ⟪b i, mildSolution (I := I) (M := M) g u_0 f s⟫_ℝ)
        ⟪b i, v⟫_ℝ t := by
      have hcomp := (innerSL (𝕜 := ℝ)
        (E := _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
        (b i)).hasFDerivAt.comp_hasDerivAt t hderiv
      simpa [Function.comp_def, innerSL_apply_apply] using hcomp
    have hmodal := hasDerivAt_mildSolution_inner_basis
      (I := I) (M := M) g u_0 hf ht i
    have hcoeff := hinner.unique hmodal
    calc
      (b.repr v) i = ⟪b i, v⟫_ℝ := HilbertBasis.repr_apply_apply b v i
      _ = -(EigenIdx.lambda (I := I) (M := M) i) *
          ⟪b i, mildSolution (I := I) (M := M) g u_0 f t⟫_ℝ + ⟪b i, f t⟫_ℝ :=
        hcoeff
      _ = ⟪b i, laplacianOp (I := I) (M := M) g u_h + f t⟫_ℝ := by
        rw [inner_add_right]
        rw [laplacianOp_inner_eigenbasis (I := I) (M := M) g u_h i]
        rw [hu_h]
      _ = (b.repr (laplacianOp (I := I) (M := M) g u_h + f t)) i :=
        (HilbertBasis.repr_apply_apply b _ i).symm
  simpa [hv] using hderiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.mildSolution_hasDerivAt_laplacianOp_add_of_lift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.mildSolution_hasDerivAt_laplacianOp_add_of_lift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.mildSolution_hasDerivAt_laplacianOp_add_of_lift ``Submission.DifferentialGeometry.Analysis.HeatEquation.mildSolution_hasDerivAt_laplacianOp_add_of_lift

theorem mildSolution_isStrongSolutionAt_of_differentiable
    (g : SmoothRiemannianMetric I M)
    (u_0 : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {f : ℝ → _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hf : Continuous f) {t : ℝ} (ht : 0 < t)
    (hdiff : DifferentiableAt ℝ (mildSolution (I := I) (M := M) g u_0 f) t)
    (u_h : laplacianDomain (I := I) (M := M) g)
    (hu_h : H1ComplToLp (I := I) (M := M) g (u_h : H1Compl g) =
      mildSolution (I := I) (M := M) g u_0 f t) :
    IsStrongSolutionAt (I := I) (M := M) g
      (mildSolution (I := I) (M := M) g u_0 f) f t := by
  refine ⟨u_h, hu_h, ?_⟩
  exact mildSolution_hasDerivAt_laplacianOp_add_of_lift
    (I := I) (M := M) g u_0 hf ht hdiff.hasDerivAt u_h hu_h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.mildSolution_isStrongSolutionAt_of_differentiable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.mildSolution_isStrongSolutionAt_of_differentiable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.mildSolution_isStrongSolutionAt_of_differentiable ``Submission.DifferentialGeometry.Analysis.HeatEquation.mildSolution_isStrongSolutionAt_of_differentiable

theorem heatSemigroup_isStrongSolutionAt
    (g : SmoothRiemannianMetric I M)
    (u_0 : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {t : ℝ} (ht : 0 < t) :
    IsStrongSolutionAt (I := I) (M := M) g
      (fun s : ℝ => heatSemigroup (I := I) (M := M) g s u_0)
      (fun _ => 0) t := by
  let u_h : laplacianDomain (I := I) (M := M) g :=
    ⟨heatSemigroupExplicitLift (I := I) (M := M) g 0 t u_0,
      heatSemigroupExplicitLift_zero_mem_laplacianDomain
        (I := I) (M := M) g t u_0⟩
  refine ⟨u_h, ?_, ?_⟩
  · exact H1ComplToLp_heatSemigroupExplicitLift (I := I) (M := M) g 0 ht u_0
  · simpa [u_h] using
      hasDerivAt_heatSemigroup_eq_laplacianOp (I := I) (M := M) g ht u_0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_isStrongSolutionAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_isStrongSolutionAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_isStrongSolutionAt ``Submission.DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_isStrongSolutionAt

theorem heatSemigroup_isStrongSolutionOn
    (g : SmoothRiemannianMetric I M)
    (u_0 : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    IsStrongSolutionOn (I := I) (M := M) g
      (fun s : ℝ => heatSemigroup (I := I) (M := M) g s u_0)
      (fun _ => 0) (Set.Ioi 0) := by
  intro t ht
  exact heatSemigroup_isStrongSolutionAt (I := I) (M := M) g u_0 ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_isStrongSolutionOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_isStrongSolutionOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_isStrongSolutionOn ``Submission.DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_isStrongSolutionOn

theorem mildSolution_zero_forcing_isStrongSolutionAt
    (g : SmoothRiemannianMetric I M)
    (u_0 : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {t : ℝ} (ht : 0 < t) :
    IsStrongSolutionAt (I := I) (M := M) g
      (mildSolution (I := I) (M := M) g u_0 (fun _ => 0))
      (fun _ => 0) t := by
  have hpath : mildSolution (I := I) (M := M) g u_0 (fun _ => 0) =
      fun s => heatSemigroup (I := I) (M := M) g s u_0 := by
    funext s
    exact mildSolution_zero_forcing (I := I) (M := M) g u_0 s
  rw [hpath]
  exact heatSemigroup_isStrongSolutionAt (I := I) (M := M) g u_0 ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.mildSolution_zero_forcing_isStrongSolutionAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.mildSolution_zero_forcing_isStrongSolutionAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.mildSolution_zero_forcing_isStrongSolutionAt ``Submission.DifferentialGeometry.Analysis.HeatEquation.mildSolution_zero_forcing_isStrongSolutionAt

theorem mildSolution_zero_forcing_isStrongSolutionOn
    (g : SmoothRiemannianMetric I M)
    (u_0 : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    IsStrongSolutionOn (I := I) (M := M) g
      (mildSolution (I := I) (M := M) g u_0 (fun _ => 0))
      (fun _ => 0) (Set.Ioi 0) := by
  intro t ht
  exact mildSolution_zero_forcing_isStrongSolutionAt
    (I := I) (M := M) g u_0 ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.mildSolution_zero_forcing_isStrongSolutionOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.mildSolution_zero_forcing_isStrongSolutionOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.mildSolution_zero_forcing_isStrongSolutionOn ``Submission.DifferentialGeometry.Analysis.HeatEquation.mildSolution_zero_forcing_isStrongSolutionOn

private lemma exp_convolution_derivative_identity
    (lam : ℝ) {t : ℝ}
    {h dh : ℝ → ℝ}
    (hderiv : ∀ s : ℝ, HasDerivAt h (dh s) s)
    (hdh : Continuous dh) :
    Real.exp (-lam * t) * h 0 +
        ∫ s in (0 : ℝ)..t, Real.exp (-lam * (t - s)) * dh s =
      -lam * (∫ s in (0 : ℝ)..t, Real.exp (-lam * (t - s)) * h s) + h t := by
  let phi : ℝ → ℝ := fun s => Real.exp (-lam * (t - s))
  have hh : Continuous h := continuous_iff_continuousAt.mpr fun s => (hderiv s).continuousAt
  have hphi : Continuous phi := by
    unfold phi
    fun_prop
  have hphi_deriv : ∀ s : ℝ, HasDerivAt phi (lam * phi s) s := by
    intro s
    have harg : HasDerivAt (fun r : ℝ => -lam * (t - r)) lam s := by
      convert ((hasDerivAt_const s t).sub (hasDerivAt_id s)).const_mul (-lam) using 1
      all_goals (try rfl)
      all_goals ring
    have hexp := harg.exp
    simpa [phi, mul_comm] using hexp
  have hprod : ∀ s : ℝ, HasDerivAt (fun r => phi r * h r)
      (lam * (phi s * h s) + phi s * dh s) s := by
    intro s
    convert (hphi_deriv s).mul (hderiv s) using 1
    all_goals (try rfl)
    all_goals ring
  have hfirst : Continuous (fun s => lam * (phi s * h s)) :=
    continuous_const.mul (hphi.mul hh)
  have hsecond : Continuous (fun s => phi s * dh s) := hphi.mul hdh
  have hsum : Continuous (fun s => lam * (phi s * h s) + phi s * dh s) := by
    exact hfirst.add hsecond
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := t) (fun s _ => hprod s) (hsum.intervalIntegrable 0 t)
  rw [intervalIntegral.integral_add (hfirst.intervalIntegrable 0 t)
      (hsecond.intervalIntegrable 0 t),
    intervalIntegral.integral_const_mul] at hftc
  have hphi_zero : phi 0 = Real.exp (-lam * t) := by simp [phi]
  have hphi_t : phi t = 1 := by simp [phi]
  rw [hphi_zero, hphi_t, one_mul] at hftc
  have hphi_identity : phi 0 * h 0 + ∫ s in (0 : ℝ)..t, phi s * dh s =
      -lam * (∫ s in (0 : ℝ)..t, phi s * h s) + h t := by
    rw [hphi_zero]
    ring_nf at hftc ⊢
    linarith
  simpa [phi] using hphi_identity

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.HeatEquation.exp_convolution_derivative_identity
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.HeatEquation.exp_convolution_derivative_identity target :: scope.openDecls } }

private theorem mildSolution_strongDerivative_inner_basis
    (g : SmoothRiemannianMetric I M)
    (u_0 : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {f f' : ℝ → _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hf : ∀ s : ℝ, HasDerivAt f (f' s) s)
    (hf' : Continuous f') {t : ℝ} (ht : 0 < t)
    (i : EigenIdx (I := I) (M := M) g) :
    ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i,
      -(heatPower (I := I) (M := M) g 1 t u_0) +
        mildSolution (I := I) (M := M) g (f 0) f' t⟫_ℝ =
      -(EigenIdx.lambda (I := I) (M := M) i) *
        ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i,
          mildSolution (I := I) (M := M) g u_0 f t⟫_ℝ +
        ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i, f t⟫_ℝ := by
  set b := resolventHilbertEigenbasisSigma (I := I) (M := M) g
  set lam := EigenIdx.lambda (I := I) (M := M) i
  let h : ℝ → ℝ := fun s => ⟪b i, f s⟫_ℝ
  let dh : ℝ → ℝ := fun s => ⟪b i, f' s⟫_ℝ
  have hf_cont : Continuous f := continuous_iff_continuousAt.mpr fun s => (hf s).continuousAt
  have hderiv : ∀ s : ℝ, HasDerivAt h (dh s) s := by
    intro s
    have hcomp := (innerSL (𝕜 := ℝ)
      (E := _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
      (b i)).hasFDerivAt.comp_hasDerivAt s (hf s)
    simpa [h, dh, Function.comp_def, innerSL_apply_apply] using hcomp
  have hdh : Continuous dh := by
    exact (innerSL (𝕜 := ℝ)
      (E := _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
      (b i)).continuous.comp hf'
  have hconv := exp_convolution_derivative_identity (t := t) lam hderiv hdh
  have horig := mildSolution_inner_basis (I := I) (M := M) g u_0 hf_cont ht.le i
  have hder := mildSolution_inner_basis (I := I) (M := M) g (f 0) hf' ht.le i
  rw [inner_add_right, inner_neg_right,
    heatPower_inner_eigenbasis (I := I) (M := M) g 1 ht i u_0,
    pow_one, hder, horig]
  change -(lam * Real.exp (-lam * t) * ⟪b i, u_0⟫_ℝ) +
      (Real.exp (-lam * t) * h 0 +
        ∫ s in (0 : ℝ)..t, Real.exp (-lam * (t - s)) * dh s) =
    -lam * (Real.exp (-lam * t) * ⟪b i, u_0⟫_ℝ +
      ∫ s in (0 : ℝ)..t, Real.exp (-lam * (t - s)) * h s) + h t
  rw [hconv]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.HeatEquation.mildSolution_strongDerivative_inner_basis
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.HeatEquation.mildSolution_strongDerivative_inner_basis target :: scope.openDecls } }

theorem mildSolution_hasDerivAt_of_hasDerivAt_forcing
    (g : SmoothRiemannianMetric I M)
    (u_0 : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {f f' : ℝ → _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hf : ∀ s : ℝ, HasDerivAt f (f' s) s)
    (hf' : Continuous f') {t : ℝ} (ht : 0 < t) :
    HasDerivAt (mildSolution (I := I) (M := M) g u_0 f)
      (-(heatPower (I := I) (M := M) g 1 t u_0) +
        mildSolution (I := I) (M := M) g (f 0) f' t) t := by
  let v : ℝ → _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
    fun s => -(heatPower (I := I) (M := M) g 1 s u_0) +
      mildSolution (I := I) (M := M) g (f 0) f' s
  have hpow : ContinuousOn
      (fun s : ℝ => heatPower (I := I) (M := M) g 1 s u_0) (Set.Ioi 0) :=
    (continuousOn_heatPower_Ioi (I := I) (M := M) g 1).clm_apply continuousOn_const
  have hmild : ContinuousOn
      (mildSolution (I := I) (M := M) g (f 0) f') (Set.Ioi 0) :=
    (mildSolution_continuous (I := I) (M := M) g (f 0) hf').mono _root_.Set.Ioi_subset_Ici_self
  have hv : ContinuousOn v (Set.Ioi 0) := hpow.neg.add hmild
  have hf_cont : Continuous f := continuous_iff_continuousAt.mpr fun s => (hf s).continuousAt
  apply hasDerivAt_of_inner_hilbertBasis
    (resolventHilbertEigenbasisSigma (I := I) (M := M) g)
    isOpen_Ioi hv
  · intro s hs i
    have hmodal := hasDerivAt_mildSolution_inner_basis
      (I := I) (M := M) g u_0 hf_cont hs i
    have hcoeff := mildSolution_strongDerivative_inner_basis
      (I := I) (M := M) g u_0 hf hf' hs i
    rw [hcoeff]
    exact hmodal
  · exact ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.mildSolution_hasDerivAt_of_hasDerivAt_forcing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.mildSolution_hasDerivAt_of_hasDerivAt_forcing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.mildSolution_hasDerivAt_of_hasDerivAt_forcing ``Submission.DifferentialGeometry.Analysis.HeatEquation.mildSolution_hasDerivAt_of_hasDerivAt_forcing

theorem mildSolution_isStrongSolutionAt_of_hasDerivAt_forcing
    (g : SmoothRiemannianMetric I M)
    (u_0 : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {f f' : ℝ → _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hf : ∀ s : ℝ, HasDerivAt f (f' s) s)
    (hf' : Continuous f') {t : ℝ} (ht : 0 < t) :
    IsStrongSolutionAt (I := I) (M := M) g
      (mildSolution (I := I) (M := M) g u_0 f) f t := by
  let derivative := -(heatPower (I := I) (M := M) g 1 t u_0) +
    mildSolution (I := I) (M := M) g (f 0) f' t
  let laplacian := derivative - f t
  have hcoeff : ∀ i : EigenIdx (I := I) (M := M) g,
      ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i, laplacian⟫_ℝ =
        -(EigenIdx.lambda (I := I) (M := M) i) *
          ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i,
            mildSolution (I := I) (M := M) g u_0 f t⟫_ℝ := by
    intro i
    rw [show laplacian = derivative - f t from rfl, inner_sub_right,
      show derivative = -(heatPower (I := I) (M := M) g 1 t u_0) +
        mildSolution (I := I) (M := M) g (f 0) f' t from rfl,
      mildSolution_strongDerivative_inner_basis
        (I := I) (M := M) g u_0 hf hf' ht i]
    ring
  obtain ⟨u_h, hu_h, hlap⟩ :=
    (exists_laplacianDomain_lift_iff_inner_eigenbasis
      (I := I) (M := M) (g := g)
      (u := mildSolution (I := I) (M := M) g u_0 f t) (w := laplacian)).mpr hcoeff
  refine ⟨u_h, hu_h, ?_⟩
  rw [hlap]
  have hderiv := mildSolution_hasDerivAt_of_hasDerivAt_forcing
    (I := I) (M := M) g u_0 hf hf' ht
  change HasDerivAt (mildSolution (I := I) (M := M) g u_0 f)
    (laplacian + f t) t
  convert hderiv using 1
  change (derivative - f t) + f t = derivative
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.mildSolution_isStrongSolutionAt_of_hasDerivAt_forcing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.mildSolution_isStrongSolutionAt_of_hasDerivAt_forcing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.mildSolution_isStrongSolutionAt_of_hasDerivAt_forcing ``Submission.DifferentialGeometry.Analysis.HeatEquation.mildSolution_isStrongSolutionAt_of_hasDerivAt_forcing

theorem mildSolution_isStrongSolutionOn_of_hasDerivAt_forcing
    (g : SmoothRiemannianMetric I M)
    (u_0 : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {f f' : ℝ → _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hf : ∀ s : ℝ, HasDerivAt f (f' s) s)
    (hf' : Continuous f') :
    IsStrongSolutionOn (I := I) (M := M) g
      (mildSolution (I := I) (M := M) g u_0 f) f (Set.Ioi 0) := by
  intro t ht
  exact mildSolution_isStrongSolutionAt_of_hasDerivAt_forcing
    (I := I) (M := M) g u_0 hf hf' ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.mildSolution_isStrongSolutionOn_of_hasDerivAt_forcing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.mildSolution_isStrongSolutionOn_of_hasDerivAt_forcing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.mildSolution_isStrongSolutionOn_of_hasDerivAt_forcing ``Submission.DifferentialGeometry.Analysis.HeatEquation.mildSolution_isStrongSolutionOn_of_hasDerivAt_forcing

theorem mildSolution_hasDerivAt_of_contDiff_forcing
    (g : SmoothRiemannianMetric I M)
    (u_0 : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {f : ℝ → _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hf : ContDiff ℝ 1 f) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (mildSolution (I := I) (M := M) g u_0 f)
      (-(heatPower (I := I) (M := M) g 1 t u_0) +
        mildSolution (I := I) (M := M) g (f 0) (deriv f) t) t := by
  apply mildSolution_hasDerivAt_of_hasDerivAt_forcing
    (I := I) (M := M) g u_0 (f' := deriv f)
  · intro s
    exact (hf.differentiable (by norm_num) s).hasDerivAt
  · exact hf.continuous_deriv_one
  · exact ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.mildSolution_hasDerivAt_of_contDiff_forcing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.mildSolution_hasDerivAt_of_contDiff_forcing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.mildSolution_hasDerivAt_of_contDiff_forcing ``Submission.DifferentialGeometry.Analysis.HeatEquation.mildSolution_hasDerivAt_of_contDiff_forcing

theorem mildSolution_isStrongSolutionOn_of_contDiff_forcing
    (g : SmoothRiemannianMetric I M)
    (u_0 : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {f : ℝ → _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hf : ContDiff ℝ 1 f) :
    IsStrongSolutionOn (I := I) (M := M) g
      (mildSolution (I := I) (M := M) g u_0 f) f (Set.Ioi 0) := by
  apply mildSolution_isStrongSolutionOn_of_hasDerivAt_forcing
    (I := I) (M := M) g u_0 (f' := deriv f)
  · intro s
    exact (hf.differentiable (by norm_num) s).hasDerivAt
  · exact hf.continuous_deriv_one

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.mildSolution_isStrongSolutionOn_of_contDiff_forcing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.mildSolution_isStrongSolutionOn_of_contDiff_forcing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.mildSolution_isStrongSolutionOn_of_contDiff_forcing ``Submission.DifferentialGeometry.Analysis.HeatEquation.mildSolution_isStrongSolutionOn_of_contDiff_forcing

end HeatEquation
end Analysis
end DifferentialGeometry

end
