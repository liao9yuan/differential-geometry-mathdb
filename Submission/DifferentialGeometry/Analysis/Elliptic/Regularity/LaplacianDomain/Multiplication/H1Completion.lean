import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.Multiplication.Smooth
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.Variational.ArbitraryTest
import Mathlib.Analysis.Normed.Operator.Extend

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Operator


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Filter _root_.Topology
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace LaplacianDomainSmoothMul

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainVariationalLimit
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainVariationalLimitGeneral

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

noncomputable def smoothScalarMulFun
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    SmoothScalar g where
  toFun := fun x : M => (φ : M → ℝ) x * v.toFun x
  smooth := φ.contMDiff.mul v.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothScalarMulFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothScalarMulFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothScalarMulFun ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothScalarMulFun

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [CompactSpace M] in
@[simp] lemma smoothScalarMulFun_toFun
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    (smoothScalarMulFun (I := I) (M := M) g φ v).toFun =
      fun x : M => (φ : M → ℝ) x * v.toFun x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothScalarMulFun_toFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothScalarMulFun_toFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothScalarMulFun_toFun ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothScalarMulFun_toFun

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [CompactSpace M] in
lemma smoothScalarMulFun_add
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v w : SmoothScalar g) :
    smoothScalarMulFun (I := I) (M := M) g φ (v + w) =
      smoothScalarMulFun (I := I) (M := M) g φ v +
        smoothScalarMulFun (I := I) (M := M) g φ w := by
  apply SmoothScalar.ext
  funext x
  change (φ : M → ℝ) x * (v + w).toFun x =
    (smoothScalarMulFun (I := I) (M := M) g φ v +
      smoothScalarMulFun (I := I) (M := M) g φ w).toFun x
  rw [SmoothScalar.toFun_add_apply,
    SmoothScalar.toFun_add_apply,
    smoothScalarMulFun_toFun, smoothScalarMulFun_toFun]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothScalarMulFun_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothScalarMulFun_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothScalarMulFun_add ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothScalarMulFun_add

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [CompactSpace M] in
lemma smoothScalarMulFun_smul
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (c : ℝ) (v : SmoothScalar g) :
    smoothScalarMulFun (I := I) (M := M) g φ (c • v) =
      c • smoothScalarMulFun (I := I) (M := M) g φ v := by
  apply SmoothScalar.ext
  funext x
  change (φ : M → ℝ) x * (c • v).toFun x =
    (c • smoothScalarMulFun (I := I) (M := M) g φ v).toFun x
  rw [SmoothScalar.toFun_smul_apply, SmoothScalar.toFun_smul_apply,
    smoothScalarMulFun_toFun]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothScalarMulFun_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothScalarMulFun_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothScalarMulFun_smul ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothScalarMulFun_smul

noncomputable def smoothScalarMulLin
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) :
    SmoothScalar g →ₗ[ℝ] SmoothScalar g where
  toFun v := smoothScalarMulFun (I := I) (M := M) g φ v
  map_add' v w := smoothScalarMulFun_add (I := I) (M := M) g φ v w
  map_smul' c v := smoothScalarMulFun_smul (I := I) (M := M) g φ c v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothScalarMulLin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothScalarMulLin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothScalarMulLin ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothScalarMulLin

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [CompactSpace M] in
omit [FiniteDimensional ℝ E] in
@[simp] lemma smoothScalarMulLin_apply
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    smoothScalarMulLin (I := I) (M := M) g φ v =
      smoothScalarMulFun (I := I) (M := M) g φ v := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothScalarMulLin_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothScalarMulLin_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothScalarMulLin_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothScalarMulLin_apply

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [CompactSpace M] in
lemma gradFun_smoothScalarMulFun
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (x : M) :
    gradFun (I := I) g (smoothScalarMulFun (I := I) (M := M) g φ v).toFun x =
      (φ : M → ℝ) x • gradFun (I := I) g v.toFun x +
        v.toFun x • gradFun (I := I) g (φ : M → ℝ) x := by
  change gradFun (I := I) g (fun y : M => (φ : M → ℝ) y * v.toFun y) x =
    (φ : M → ℝ) x • gradFun (I := I) g v.toFun x +
      v.toFun x • gradFun (I := I) g (φ : M → ℝ) x
  exact LaplacianDomainVariationalLimitGeneral.gradFun_smul_smooth_eq_pointwise
    (I := I) (M := M) g φ.contMDiff v.smooth x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.gradFun_smoothScalarMulFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.gradFun_smoothScalarMulFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.gradFun_smoothScalarMulFun ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.gradFun_smoothScalarMulFun

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    in
private lemma sq_phi_mul_v_le
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (x : M) :
    ((φ : M → ℝ) x * v.toFun x) ^ 2 ≤
      phiSupBound (I := I) (M := M) g φ ^ 2 * v.toFun x ^ 2 := by
  have h_abs := abs_phi_le_phiSupBound (I := I) (M := M) g φ x
  have h_abs_nn : (0 : ℝ) ≤ |((φ : M → ℝ) x)| := abs_nonneg _
  have h_v_sq_nn : (0 : ℝ) ≤ v.toFun x ^ 2 := sq_nonneg _
  have h_phi_sq_le : ((φ : M → ℝ) x) ^ 2 ≤ phiSupBound (I := I) (M := M) g φ ^ 2 := by
    have h_sq_eq : ((φ : M → ℝ) x) ^ 2 = |((φ : M → ℝ) x)| ^ 2 := (sq_abs _).symm
    rw [h_sq_eq]
    exact pow_le_pow_left₀ h_abs_nn h_abs 2
  have h_eq : ((φ : M → ℝ) x * v.toFun x) ^ 2 =
      ((φ : M → ℝ) x) ^ 2 * v.toFun x ^ 2 := by ring
  rw [h_eq]
  exact mul_le_mul_of_nonneg_right h_phi_sq_le h_v_sq_nn

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.sq_phi_mul_v_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.sq_phi_mul_v_le target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [CompactSpace M] in
private lemma metric_inner_self_nonneg
    (g : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    0 ≤ g.inner x v v :=
  SmoothRiemannianMetric_inner_self_nonneg g x v

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.metric_inner_self_nonneg
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.metric_inner_self_nonneg target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [CompactSpace M] in
private lemma inner_grad_self_nonneg
    (g : SmoothRiemannianMetric I M) (φ : M → ℝ) (x : M) :
    0 ≤ g.inner x (gradFun (I := I) g φ x) (gradFun (I := I) g φ x) :=
  metric_inner_self_nonneg (I := I) (M := M) g x _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.inner_grad_self_nonneg
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.inner_grad_self_nonneg target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [CompactSpace M] in
private lemma inner_grad_phi_mul_v_le
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (x : M) :
    g.inner x (gradFun (I := I) g
        (smoothScalarMulFun (I := I) (M := M) g φ v).toFun x)
      (gradFun (I := I) g
        (smoothScalarMulFun (I := I) (M := M) g φ v).toFun x) ≤
    2 * (((φ : M → ℝ) x) ^ 2 *
        g.inner x (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x)) +
      2 * ((v.toFun x) ^ 2 *
        g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g (φ : M → ℝ) x)) := by
  rw [gradFun_smoothScalarMulFun]
  set A : TangentSpace I x := (φ : M → ℝ) x • gradFun (I := I) g v.toFun x
  set B : TangentSpace I x := v.toFun x • gradFun (I := I) g (φ : M → ℝ) x
  have h_expand :
      g.inner x (A + B) (A + B) =
        g.inner x A A + 2 * g.inner x A B + g.inner x B B := by
    have h1 : g.inner x (A + B) (A + B) =
        g.inner x A (A + B) + g.inner x B (A + B) := by
      rw [(g.inner x).map_add]; rfl
    rw [h1]
    have h_A_split : g.inner x A (A + B) = g.inner x A A + g.inner x A B :=
      (g.inner x A).map_add A B
    have h_B_split : g.inner x B (A + B) = g.inner x B A + g.inner x B B :=
      (g.inner x B).map_add A B
    have h_BA_eq_AB : g.inner x B A = g.inner x A B := g.symm x B A
    rw [h_A_split, h_B_split, h_BA_eq_AB]
    ring
  rw [h_expand]
  have h_CS_bound : 2 * g.inner x A B ≤ g.inner x A A + g.inner x B B := by
    have h_abs_CS : |g.inner x A B| ≤
        Real.sqrt (g.inner x A A) * Real.sqrt (g.inner x B B) :=
      abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g x A B
    have h_AA_nn := metric_inner_self_nonneg (I := I) (M := M) g x A
    have h_BB_nn := metric_inner_self_nonneg (I := I) (M := M) g x B
    have h_AM : 2 * (Real.sqrt (g.inner x A A) * Real.sqrt (g.inner x B B)) ≤
        (Real.sqrt (g.inner x A A)) ^ 2 + (Real.sqrt (g.inner x B B)) ^ 2 := by
      have : 0 ≤ (Real.sqrt (g.inner x A A) - Real.sqrt (g.inner x B B)) ^ 2 :=
        sq_nonneg _
      nlinarith
    have h_sqrt_sq_A : (Real.sqrt (g.inner x A A)) ^ 2 = g.inner x A A :=
      Real.sq_sqrt h_AA_nn
    have h_sqrt_sq_B : (Real.sqrt (g.inner x B B)) ^ 2 = g.inner x B B :=
      Real.sq_sqrt h_BB_nn
    rw [h_sqrt_sq_A, h_sqrt_sq_B] at h_AM
    have h_2abs_le : 2 * |g.inner x A B| ≤
        2 * (Real.sqrt (g.inner x A A) * Real.sqrt (g.inner x B B)) := by
      have h_abs_nn : 0 ≤ |g.inner x A B| := abs_nonneg _
      linarith
    have h_le_abs : g.inner x A B ≤ |g.inner x A B| := le_abs_self _
    linarith
  have h_AA : g.inner x A A =
      ((φ : M → ℝ) x) ^ 2 *
        g.inner x (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x) := by
    change g.inner x ((φ : M → ℝ) x • gradFun (I := I) g v.toFun x)
        ((φ : M → ℝ) x • gradFun (I := I) g v.toFun x) =
      ((φ : M → ℝ) x) ^ 2 *
        g.inner x (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x)
    rw [(g.inner x).map_smul, smul_apply,
      (g.inner x _).map_smul]
    change (φ : M → ℝ) x • (φ : M → ℝ) x •
        g.inner x (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x) =
      ((φ : M → ℝ) x) ^ 2 *
        g.inner x (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x)
    rw [smul_eq_mul, smul_eq_mul]
    ring
  have h_BB : g.inner x B B =
      (v.toFun x) ^ 2 *
        g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g (φ : M → ℝ) x) := by
    change g.inner x (v.toFun x • gradFun (I := I) g (φ : M → ℝ) x)
        (v.toFun x • gradFun (I := I) g (φ : M → ℝ) x) =
      (v.toFun x) ^ 2 *
        g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g (φ : M → ℝ) x)
    rw [(g.inner x).map_smul, smul_apply,
      (g.inner x _).map_smul]
    change v.toFun x • v.toFun x •
        g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g (φ : M → ℝ) x) =
      (v.toFun x) ^ 2 *
        g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g (φ : M → ℝ) x)
    rw [smul_eq_mul, smul_eq_mul]
    ring
  rw [h_AA, h_BB] at h_CS_bound ⊢
  linarith [h_CS_bound]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.inner_grad_phi_mul_v_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.inner_grad_phi_mul_v_le target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma integral_sq_phi_mul_v_le
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    (∫ x, ((φ : M → ℝ) x * v.toFun x) ^ 2
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
      phiSupBound (I := I) (M := M) g φ ^ 2 *
        (∫ x, v.toFun x ^ 2
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
  have : _root_.MeasureTheory.IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  have h_phi_cont : Continuous (φ : M → ℝ) := φ.contMDiff.continuous
  have h_v_cont : Continuous v.toFun := v.smooth.continuous
  have h_LHS_cont : Continuous (fun x : M => ((φ : M → ℝ) x * v.toFun x) ^ 2) :=
    (h_phi_cont.mul h_v_cont).pow 2
  have h_RHS_cont : Continuous (fun x : M => v.toFun x ^ 2) := h_v_cont.pow 2
  have h_LHS_int : _root_.MeasureTheory.Integrable (fun x : M => ((φ : M → ℝ) x * v.toFun x) ^ 2)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    h_LHS_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h_RHS_int : _root_.MeasureTheory.Integrable (fun x : M => v.toFun x ^ 2)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    h_RHS_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h_RHS_cmul_int : _root_.MeasureTheory.Integrable (fun x : M =>
      phiSupBound (I := I) (M := M) g φ ^ 2 * v.toFun x ^ 2)
      (riemannianVolumeMeasure (I := I) (M := M) g) := h_RHS_int.const_mul _
  have h_pt : ∀ x : M, ((φ : M → ℝ) x * v.toFun x) ^ 2 ≤
      phiSupBound (I := I) (M := M) g φ ^ 2 * v.toFun x ^ 2 :=
    sq_phi_mul_v_le (I := I) (M := M) g φ v
  have h_int_le := _root_.MeasureTheory.integral_mono_ae h_LHS_int h_RHS_cmul_int
    (Filter.Eventually.of_forall h_pt)
  rw [_root_.MeasureTheory.integral_const_mul] at h_int_le
  exact h_int_le

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.integral_sq_phi_mul_v_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.integral_sq_phi_mul_v_le target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma integral_inner_grad_phi_mul_v_le
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    (∫ x, g.inner x (gradFun (I := I) g
          (smoothScalarMulFun (I := I) (M := M) g φ v).toFun x)
        (gradFun (I := I) g
          (smoothScalarMulFun (I := I) (M := M) g φ v).toFun x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
      2 * phiSupBound (I := I) (M := M) g φ ^ 2 *
        (∫ x, g.inner x (gradFun (I := I) g v.toFun x)
              (gradFun (I := I) g v.toFun x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
      2 * gradSupBound (I := I) (M := M) g φ ^ 2 *
        (∫ x, v.toFun x ^ 2
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
  have : _root_.MeasureTheory.IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  have h_phi_cont : Continuous (φ : M → ℝ) := φ.contMDiff.continuous
  have h_v_cont : Continuous v.toFun := v.smooth.continuous
  have h_inner_eq_v : ∀ x : M,
      g.inner x ((gradG (I := I) g ⟨v.toFun, v.smooth⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((gradG (I := I) g ⟨v.toFun, v.smooth⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
      g.inner x (gradFun (I := I) g v.toFun x)
        (gradFun (I := I) g v.toFun x) := by
    intro x; rfl
  have h_inner_cont_v : Continuous (fun x : M => g.inner x
      (gradFun (I := I) g v.toFun x)
      (gradFun (I := I) g v.toFun x)) :=
    (TangentBundle.continuous_g_inner_of_smooth_sections (I := I) (M := M) g
      (gradG (I := I) g ⟨v.toFun, v.smooth⟩) (gradG (I := I) g ⟨v.toFun,
        v.smooth⟩)).congr h_inner_eq_v
  have h_inner_eq_phi : ∀ x : M,
      g.inner x ((gradG (I := I) g φ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((gradG (I := I) g φ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
      g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
        (gradFun (I := I) g (φ : M → ℝ) x) := by
    intro x; rfl
  have h_inner_cont_phi : Continuous (fun x : M => g.inner x
      (gradFun (I := I) g (φ : M → ℝ) x)
      (gradFun (I := I) g (φ : M → ℝ) x)) :=
    (TangentBundle.continuous_g_inner_of_smooth_sections (I := I) (M := M) g
      (gradG (I := I) g φ)
        (gradG (I := I) g φ)).congr h_inner_eq_phi
  have h_inner_eq_phiv : ∀ x : M,
      g.inner x ((gradG (I := I) g ⟨(smoothScalarMulFun (I := I) (M := M) g φ v).toFun,
        (smoothScalarMulFun (I := I) (M := M) g φ v).smooth⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((gradG (I := I) g ⟨(smoothScalarMulFun (I := I) (M := M) g φ v).toFun,
          (smoothScalarMulFun (I := I) (M := M) g φ v).smooth⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
      g.inner x (gradFun (I := I) g
          (smoothScalarMulFun (I := I) (M := M) g φ v).toFun x)
        (gradFun (I := I) g
          (smoothScalarMulFun (I := I) (M := M) g φ v).toFun x) := by
    intro x; rfl
  have h_LHS_cont : Continuous (fun x : M =>
      g.inner x (gradFun (I := I) g
          (smoothScalarMulFun (I := I) (M := M) g φ v).toFun x)
        (gradFun (I := I) g
          (smoothScalarMulFun (I := I) (M := M) g φ v).toFun x)) :=
    (TangentBundle.continuous_g_inner_of_smooth_sections (I := I) (M := M) g
      (gradG (I := I) g ⟨(smoothScalarMulFun (I := I) (M := M) g φ v).toFun,
        (smoothScalarMulFun (I := I) (M := M) g φ v).smooth⟩)
        (gradG (I := I) g ⟨(smoothScalarMulFun (I := I) (M := M) g φ v).toFun,
          (smoothScalarMulFun (I := I) (M := M) g φ v).smooth⟩)).congr h_inner_eq_phiv
  have h_grad_phi2_v_v_cont : Continuous (fun x : M =>
      ((φ : M → ℝ) x) ^ 2 *
        g.inner x (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x)) :=
    (h_phi_cont.pow 2).mul h_inner_cont_v
  have h_grad_v2_phi_phi_cont : Continuous (fun x : M =>
      (v.toFun x) ^ 2 *
        g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g (φ : M → ℝ) x)) :=
    (h_v_cont.pow 2).mul h_inner_cont_phi
  have h_LHS_int : _root_.MeasureTheory.Integrable _
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    h_LHS_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h_RHS1_int : _root_.MeasureTheory.Integrable (fun x : M =>
      ((φ : M → ℝ) x) ^ 2 *
        g.inner x (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    h_grad_phi2_v_v_cont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h_RHS2_int : _root_.MeasureTheory.Integrable (fun x : M =>
      (v.toFun x) ^ 2 *
        g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g (φ : M → ℝ) x))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    h_grad_v2_phi_phi_cont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h_RHS_int : _root_.MeasureTheory.Integrable (fun x : M =>
      2 * (((φ : M → ℝ) x) ^ 2 *
        g.inner x (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x)) +
      2 * ((v.toFun x) ^ 2 *
        g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g (φ : M → ℝ) x)))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    (h_RHS1_int.const_mul 2).add (h_RHS2_int.const_mul 2)
  have h_pt : ∀ x : M, g.inner x (gradFun (I := I) g
          (smoothScalarMulFun (I := I) (M := M) g φ v).toFun x)
        (gradFun (I := I) g
          (smoothScalarMulFun (I := I) (M := M) g φ v).toFun x) ≤
      2 * (((φ : M → ℝ) x) ^ 2 *
        g.inner x (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x)) +
      2 * ((v.toFun x) ^ 2 *
        g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g (φ : M → ℝ) x)) :=
    inner_grad_phi_mul_v_le (I := I) (M := M) g φ v
  have h_int_le := _root_.MeasureTheory.integral_mono_ae h_LHS_int h_RHS_int
    (Filter.Eventually.of_forall h_pt)
  have h_int_eq : (∫ x, 2 * (((φ : M → ℝ) x) ^ 2 *
        g.inner x (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x)) +
      2 * ((v.toFun x) ^ 2 *
        g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g (φ : M → ℝ) x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
    2 * (∫ x, (((φ : M → ℝ) x) ^ 2 *
          g.inner x (gradFun (I := I) g v.toFun x)
            (gradFun (I := I) g v.toFun x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
    2 * (∫ x, ((v.toFun x) ^ 2 *
          g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
            (gradFun (I := I) g (φ : M → ℝ) x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
    rw [_root_.MeasureTheory.integral_add (h_RHS1_int.const_mul 2) (h_RHS2_int.const_mul 2),
      _root_.MeasureTheory.integral_const_mul, _root_.MeasureTheory.integral_const_mul]
  rw [h_int_eq] at h_int_le
  have h_int1_le : (∫ x, (((φ : M → ℝ) x) ^ 2 *
        g.inner x (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
      phiSupBound (I := I) (M := M) g φ ^ 2 *
        (∫ x, g.inner x (gradFun (I := I) g v.toFun x)
              (gradFun (I := I) g v.toFun x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
    have h_pt1 : ∀ x : M, ((φ : M → ℝ) x) ^ 2 *
        g.inner x (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x) ≤
        phiSupBound (I := I) (M := M) g φ ^ 2 *
        g.inner x (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x) := by
      intro x
      have h_inner_nn := inner_grad_self_nonneg (I := I) (M := M) g v.toFun x
      have h_phi_sq_le : ((φ : M → ℝ) x) ^ 2 ≤
          phiSupBound (I := I) (M := M) g φ ^ 2 := by
        have h_abs := abs_phi_le_phiSupBound (I := I) (M := M) g φ x
        have h_abs_nn : (0 : ℝ) ≤ |((φ : M → ℝ) x)| := abs_nonneg _
        have h_sq_eq : ((φ : M → ℝ) x) ^ 2 = |((φ : M → ℝ) x)| ^ 2 := (sq_abs _).symm
        rw [h_sq_eq]
        exact pow_le_pow_left₀ h_abs_nn h_abs 2
      exact mul_le_mul_of_nonneg_right h_phi_sq_le h_inner_nn
    have h_inner_v_int : _root_.MeasureTheory.Integrable (fun x : M => g.inner x
        (gradFun (I := I) g v.toFun x) (gradFun (I := I) g v.toFun x))
        (riemannianVolumeMeasure (I := I) (M := M) g) :=
      h_inner_cont_v.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have h_cmul_int := h_inner_v_int.const_mul (phiSupBound (I := I) (M := M) g φ ^ 2)
    have := _root_.MeasureTheory.integral_mono_ae h_RHS1_int h_cmul_int (Filter.Eventually.of_forall h_pt1)
    rw [_root_.MeasureTheory.integral_const_mul] at this
    exact this
  have h_int2_le : (∫ x, ((v.toFun x) ^ 2 *
        g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g (φ : M → ℝ) x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
      gradSupBound (I := I) (M := M) g φ ^ 2 *
        (∫ x, v.toFun x ^ 2
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
    have h_pt2 : ∀ x : M, (v.toFun x) ^ 2 *
        g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g (φ : M → ℝ) x) ≤
        gradSupBound (I := I) (M := M) g φ ^ 2 *
        v.toFun x ^ 2 := by
      intro x
      have h_v_sq_nn : (0 : ℝ) ≤ v.toFun x ^ 2 := sq_nonneg _
      have h_inner_phi_nn := inner_grad_self_nonneg (I := I) (M := M) g (φ : M → ℝ) x
      have h_sqrt_le := sqrt_inner_grad_self_le_gradSupBound (I := I) (M := M) g φ x
      have h_sqrt_nn : 0 ≤ Real.sqrt (g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g (φ : M → ℝ) x)) := Real.sqrt_nonneg _
      have h_inner_eq : (Real.sqrt (g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g (φ : M → ℝ) x))) ^ 2 =
          g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g (φ : M → ℝ) x) := Real.sq_sqrt h_inner_phi_nn
      have h_inner_le : g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g (φ : M → ℝ) x) ≤
          gradSupBound (I := I) (M := M) g φ ^ 2 := by
        calc g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
              (gradFun (I := I) g (φ : M → ℝ) x) =
            (Real.sqrt (g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
              (gradFun (I := I) g (φ : M → ℝ) x))) ^ 2 := h_inner_eq.symm
          _ ≤ gradSupBound (I := I) (M := M) g φ ^ 2 :=
            pow_le_pow_left₀ h_sqrt_nn h_sqrt_le 2
      calc (v.toFun x) ^ 2 * g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
              (gradFun (I := I) g (φ : M → ℝ) x) ≤
          (v.toFun x) ^ 2 * gradSupBound (I := I) (M := M) g φ ^ 2 :=
            mul_le_mul_of_nonneg_left h_inner_le h_v_sq_nn
        _ = gradSupBound (I := I) (M := M) g φ ^ 2 * v.toFun x ^ 2 := by ring
    have h_v_sq_int : _root_.MeasureTheory.Integrable (fun x : M => v.toFun x ^ 2)
        (riemannianVolumeMeasure (I := I) (M := M) g) := by
      have h_v_sq_cont : Continuous (fun x : M => v.toFun x ^ 2) := h_v_cont.pow 2
      exact h_v_sq_cont.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have h_cmul_int := h_v_sq_int.const_mul (gradSupBound (I := I) (M := M) g φ ^ 2)
    have := _root_.MeasureTheory.integral_mono_ae h_RHS2_int h_cmul_int (Filter.Eventually.of_forall h_pt2)
    rw [_root_.MeasureTheory.integral_const_mul] at this
    exact this
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.integral_inner_grad_phi_mul_v_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.integral_inner_grad_phi_mul_v_le target :: scope.openDecls } }

noncomputable def smoothMulH1ComplConst
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) : ℝ :=
  Real.sqrt (2 * (phiSupBound (I := I) (M := M) g φ ^ 2 +
    gradSupBound (I := I) (M := M) g φ ^ 2))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulH1ComplConst then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulH1ComplConst"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulH1ComplConst ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulH1ComplConst

omit [NeZero (Module.finrank ℝ E)] [T2Space M] in
lemma smoothMulH1ComplConst_nonneg
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) :
    0 ≤ smoothMulH1ComplConst (I := I) (M := M) g φ :=
  Real.sqrt_nonneg _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulH1ComplConst_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulH1ComplConst_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulH1ComplConst_nonneg ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulH1ComplConst_nonneg

omit [NeZero (Module.finrank ℝ E)] [T2Space M] in
lemma smoothMulH1ComplConst_sq
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) :
    smoothMulH1ComplConst (I := I) (M := M) g φ ^ 2 =
      2 * (phiSupBound (I := I) (M := M) g φ ^ 2 +
        gradSupBound (I := I) (M := M) g φ ^ 2) := by
  unfold smoothMulH1ComplConst
  rw [Real.sq_sqrt]
  have h_phi_nn := sq_nonneg (phiSupBound (I := I) (M := M) g φ)
  have h_grad_nn := sq_nonneg (gradSupBound (I := I) (M := M) g φ)
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulH1ComplConst_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulH1ComplConst_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulH1ComplConst_sq ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulH1ComplConst_sq

omit [NeZero (Module.finrank ℝ E)] in
theorem norm_smoothScalarMulFun_sq_le
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    ‖smoothScalarMulFun (I := I) (M := M) g φ v‖ ^ 2 ≤
      smoothMulH1ComplConst (I := I) (M := M) g φ ^ 2 * ‖v‖ ^ 2 := by
  rw [SmoothScalar.norm_sq_eq_inner_self,
    SmoothScalar.norm_sq_eq_inner_self v]
  unfold smoothScalarH1Inner
  rw [smoothMulH1ComplConst_sq]
  have h_lhs_l2 : (∫ x, (smoothScalarMulFun (I := I) (M := M) g φ v).toFun x *
        (smoothScalarMulFun (I := I) (M := M) g φ v).toFun x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      (∫ x, ((φ : M → ℝ) x * v.toFun x) ^ 2
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
    refine _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x
    change ((φ : M → ℝ) x * v.toFun x) * ((φ : M → ℝ) x * v.toFun x) =
      ((φ : M → ℝ) x * v.toFun x) ^ 2
    rw [sq]
  rw [h_lhs_l2]
  have h_rhs_l2 : (∫ x, v.toFun x * v.toFun x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      (∫ x, v.toFun x ^ 2
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
    refine _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x
    change v.toFun x * v.toFun x = v.toFun x ^ 2
    rw [sq]
  rw [h_rhs_l2]
  have h_grad_int_v : (∫ x, g.inner x
        ((gradG (I := I) g ⟨v.toFun, v.smooth⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((gradG (I := I) g ⟨v.toFun, v.smooth⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      (∫ x, g.inner x (gradFun (I := I) g v.toFun x)
        (gradFun (I := I) g v.toFun x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
    refine _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x; rfl
  have h_grad_int_phiv : (∫ x, g.inner x
        ((gradG (I := I) g ⟨(smoothScalarMulFun (I := I) (M := M) g φ v).toFun,
          (smoothScalarMulFun (I := I) (M := M) g φ v).smooth⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((gradG (I := I) g ⟨(smoothScalarMulFun (I := I) (M := M) g φ v).toFun,
          (smoothScalarMulFun (I := I) (M := M) g φ v).smooth⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      (∫ x, g.inner x (gradFun (I := I) g
          (smoothScalarMulFun (I := I) (M := M) g φ v).toFun x)
        (gradFun (I := I) g
          (smoothScalarMulFun (I := I) (M := M) g φ v).toFun x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
    refine _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x; rfl
  rw [h_grad_int_v, h_grad_int_phiv]
  have h_l2_le := integral_sq_phi_mul_v_le (I := I) (M := M) g φ v
  have h_grad_le := integral_inner_grad_phi_mul_v_le (I := I) (M := M) g φ v
  have h_v_l2_nn : 0 ≤ ∫ x, v.toFun x ^ 2
      ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    refine _root_.MeasureTheory.integral_nonneg ?_; intro x; exact sq_nonneg _
  have h_v_grad_nn : 0 ≤ ∫ x, g.inner x (gradFun (I := I) g v.toFun x)
      (gradFun (I := I) g v.toFun x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    refine _root_.MeasureTheory.integral_nonneg ?_; intro x
    exact inner_grad_self_nonneg (I := I) (M := M) g v.toFun x
  have h_phi_sq_nn := sq_nonneg (phiSupBound (I := I) (M := M) g φ)
  have h_grad_sq_nn := sq_nonneg (gradSupBound (I := I) (M := M) g φ)
  nlinarith [h_l2_le, h_grad_le]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.norm_smoothScalarMulFun_sq_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.norm_smoothScalarMulFun_sq_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.norm_smoothScalarMulFun_sq_le ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.norm_smoothScalarMulFun_sq_le

omit [NeZero (Module.finrank ℝ E)] in
theorem norm_smoothScalarMulFun_le
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    ‖smoothScalarMulFun (I := I) (M := M) g φ v‖ ≤
      smoothMulH1ComplConst (I := I) (M := M) g φ * ‖v‖ := by
  have h_sq := norm_smoothScalarMulFun_sq_le (I := I) (M := M) g φ v
  have h_lhs_nn : 0 ≤ ‖smoothScalarMulFun (I := I) (M := M) g φ v‖ := norm_nonneg _
  have h_rhs_nn : 0 ≤ smoothMulH1ComplConst (I := I) (M := M) g φ * ‖v‖ :=
    mul_nonneg (smoothMulH1ComplConst_nonneg (I := I) (M := M) g φ) (norm_nonneg _)
  have h_sq_le : ‖smoothScalarMulFun (I := I) (M := M) g φ v‖ ^ 2 ≤
      (smoothMulH1ComplConst (I := I) (M := M) g φ * ‖v‖) ^ 2 := by
    have h_eq : (smoothMulH1ComplConst (I := I) (M := M) g φ * ‖v‖) ^ 2 =
        smoothMulH1ComplConst (I := I) (M := M) g φ ^ 2 * ‖v‖ ^ 2 := by ring
    rw [h_eq]
    exact h_sq
  exact abs_le_of_sq_le_sq' h_sq_le h_rhs_nn |>.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.norm_smoothScalarMulFun_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.norm_smoothScalarMulFun_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.norm_smoothScalarMulFun_le ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.norm_smoothScalarMulFun_le

omit [NeZero (Module.finrank ℝ E)] in
private lemma norm_smoothScalarMulLin_le
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    ‖smoothScalarMulLin (I := I) (M := M) g φ v‖ ≤
      smoothMulH1ComplConst (I := I) (M := M) g φ * ‖v‖ :=
  norm_smoothScalarMulFun_le (I := I) (M := M) g φ v

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.norm_smoothScalarMulLin_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.norm_smoothScalarMulLin_le target :: scope.openDecls } }

noncomputable def smoothScalarMul
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) :
    SmoothScalar g →L[ℝ] SmoothScalar g :=
  (smoothScalarMulLin (I := I) (M := M) g φ).mkContinuous
    (smoothMulH1ComplConst (I := I) (M := M) g φ)
    (fun v => norm_smoothScalarMulLin_le (I := I) (M := M) g φ v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothScalarMul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothScalarMul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothScalarMul ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothScalarMul

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma smoothScalarMul_apply
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    smoothScalarMul (I := I) (M := M) g φ v =
      smoothScalarMulFun (I := I) (M := M) g φ v := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothScalarMul_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothScalarMul_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothScalarMul_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothScalarMul_apply

private noncomputable def smoothMulH1ComplOnSmooth
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) :
    SmoothScalar g →L[ℝ] H1Compl g :=
  (smoothToH1Compl (I := I) (M := M) g).comp
    (smoothScalarMul (I := I) (M := M) g φ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulH1ComplOnSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulH1ComplOnSmooth target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
@[simp] private lemma smoothMulH1ComplOnSmooth_apply
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    smoothMulH1ComplOnSmooth (I := I) (M := M) g φ v =
      smoothToH1Compl (I := I) (M := M) g
        (smoothScalarMulFun (I := I) (M := M) g φ v) := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulH1ComplOnSmooth_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulH1ComplOnSmooth_apply target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma denseRange_toComplL_smoothScalar
    (g : SmoothRiemannianMetric I M) :
    DenseRange (UniformSpace.Completion.toComplL :
      SmoothScalar g →L[ℝ] H1Compl g) := by
  rw [show (UniformSpace.Completion.toComplL : SmoothScalar g → H1Compl g) =
      ((↑) : SmoothScalar g → UniformSpace.Completion (SmoothScalar g)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.denseRange_coe

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.denseRange_toComplL_smoothScalar
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.denseRange_toComplL_smoothScalar target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma isUniformInducing_toComplL_smoothScalar
    (g : SmoothRiemannianMetric I M) :
    IsUniformInducing
      (UniformSpace.Completion.toComplL :
        SmoothScalar g →L[ℝ] H1Compl g) := by
  rw [show (UniformSpace.Completion.toComplL : SmoothScalar g → H1Compl g) =
      ((↑) : SmoothScalar g → UniformSpace.Completion (SmoothScalar g)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.isUniformInducing_coe (SmoothScalar g)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.isUniformInducing_toComplL_smoothScalar
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.isUniformInducing_toComplL_smoothScalar target :: scope.openDecls } }

noncomputable def smoothMulH1Compl
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) :
    H1Compl g →L[ℝ] H1Compl g :=
  ContinuousLinearMap.extend (smoothMulH1ComplOnSmooth (I := I) (M := M) g φ)
    (UniformSpace.Completion.toComplL :
      SmoothScalar g →L[ℝ] H1Compl g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulH1Compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulH1Compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulH1Compl ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulH1Compl

omit [NeZero (Module.finrank ℝ E)] in
theorem smoothMulH1Compl_smoothToH1Compl
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    smoothMulH1Compl (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) =
      smoothToH1Compl (I := I) (M := M) g
        (smoothScalarMulFun (I := I) (M := M) g φ v) := by
  unfold smoothMulH1Compl
  exact ContinuousLinearMap.extend_eq
    (smoothMulH1ComplOnSmooth (I := I) (M := M) g φ)
    (e := UniformSpace.Completion.toComplL)
    (denseRange_toComplL_smoothScalar (I := I) (M := M) g)
    (isUniformInducing_toComplL_smoothScalar (I := I) (M := M) g) v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulH1Compl_smoothToH1Compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulH1Compl_smoothToH1Compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulH1Compl_smoothToH1Compl ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulH1Compl_smoothToH1Compl

omit [NeZero (Module.finrank ℝ E)] in
private lemma H1ComplToLp_smoothMulH1Compl_eq_smoothMulLp_H1ComplToLp_on_smooth
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    H1ComplToLp (I := I) (M := M) g
        (smoothMulH1Compl (I := I) (M := M) g φ
          (smoothToH1Compl (I := I) (M := M) g v)) =
      smoothMulLp (I := I) (M := M) g φ
        (H1ComplToLp (I := I) (M := M) g
          (smoothToH1Compl (I := I) (M := M) g v)) := by
  rw [smoothMulH1Compl_smoothToH1Compl, H1ComplToLp_smoothToH1Compl,
    H1ComplToLp_smoothToH1Compl]
  apply MeasureTheory.Lp.ext
  have h_lhs_aeEq : (smoothToLp (I := I) (M := M) g
          (smoothScalarMulFun (I := I) (M := M) g φ v) :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      fun x : M => (φ : M → ℝ) x * v.toFun x := by
    have h := MemLp.coeFn_toLp
      (smoothScalarMulFun (I := I) (M := M) g φ v).memLp_two
    refine h.trans ?_
    refine Filter.Eventually.of_forall ?_
    intro x; rfl
  have h_smoothToLp_v_aeEq : (smoothToLp (I := I) (M := M) g v :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g] v.toFun :=
    MemLp.coeFn_toLp v.memLp_two
  have h_rhs_aeEq := smoothMulLp_apply_coeFn (I := I) (M := M) g φ
    (smoothToLp (I := I) (M := M) g v)
  refine h_lhs_aeEq.trans ?_
  refine EventuallyEq.symm ?_
  filter_upwards [h_rhs_aeEq, h_smoothToLp_v_aeEq] with x h_rhs h_v
  rw [h_rhs, h_v]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.H1ComplToLp_smoothMulH1Compl_eq_smoothMulLp_H1ComplToLp_on_smooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.H1ComplToLp_smoothMulH1Compl_eq_smoothMulLp_H1ComplToLp_on_smooth target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
theorem H1ComplToLp_smoothMulH1Compl_eq_smoothMulLp_H1ComplToLp
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) :
    (H1ComplToLp (I := I) (M := M) g).comp
        (smoothMulH1Compl (I := I) (M := M) g φ) =
      (smoothMulLp (I := I) (M := M) g φ).comp
        (H1ComplToLp (I := I) (M := M) g) := by
  have h_dense := denseRange_toComplL_smoothScalar (I := I) (M := M) g
  apply ContinuousLinearMap.ext
  intro u
  refine h_dense.induction_on (p := fun u => _ = _) u ?_ ?_
  · refine isClosed_eq ?_ ?_
    · exact ((H1ComplToLp (I := I) (M := M) g).comp
        (smoothMulH1Compl (I := I) (M := M) g φ)).continuous
    · exact ((smoothMulLp (I := I) (M := M) g φ).comp
        (H1ComplToLp (I := I) (M := M) g)).continuous
  · intro v
    show ((H1ComplToLp (I := I) (M := M) g).comp
        (smoothMulH1Compl (I := I) (M := M) g φ))
          (UniformSpace.Completion.toComplL v) =
      ((smoothMulLp (I := I) (M := M) g φ).comp
        (H1ComplToLp (I := I) (M := M) g))
          (UniformSpace.Completion.toComplL v)
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    exact H1ComplToLp_smoothMulH1Compl_eq_smoothMulLp_H1ComplToLp_on_smooth
      (I := I) (M := M) g φ v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.H1ComplToLp_smoothMulH1Compl_eq_smoothMulLp_H1ComplToLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.H1ComplToLp_smoothMulH1Compl_eq_smoothMulLp_H1ComplToLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.H1ComplToLp_smoothMulH1Compl_eq_smoothMulLp_H1ComplToLp ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.H1ComplToLp_smoothMulH1Compl_eq_smoothMulLp_H1ComplToLp

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem H1ComplToLp_smoothMulH1Compl
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (u : H1Compl g) :
    H1ComplToLp (I := I) (M := M) g (smoothMulH1Compl (I := I) (M := M) g φ u) =
      smoothMulLp (I := I) (M := M) g φ
        (H1ComplToLp (I := I) (M := M) g u) := by
  have h := H1ComplToLp_smoothMulH1Compl_eq_smoothMulLp_H1ComplToLp
    (I := I) (M := M) g φ
  exact congrArg (fun f => f u) h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.H1ComplToLp_smoothMulH1Compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.H1ComplToLp_smoothMulH1Compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.H1ComplToLp_smoothMulH1Compl ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.H1ComplToLp_smoothMulH1Compl

noncomputable def smoothLaplacianBundle
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) :
    C^∞⟮I, M; ℝ⟯ :=
  ⟨ΔG (I := I) g φ,
    Δ_g_contMDiff (I := I) g φ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothLaplacianBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothLaplacianBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothLaplacianBundle ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothLaplacianBundle

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
@[simp] lemma smoothLaplacianBundle_apply
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (x : M) :
    (smoothLaplacianBundle (I := I) (M := M) g φ : M → ℝ) x =
      ΔG (I := I) g φ x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothLaplacianBundle_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothLaplacianBundle_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothLaplacianBundle_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothLaplacianBundle_apply

noncomputable def leibnizCompensatedSourceResidualCLMOfSmoothFactor
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) :
    H1Compl (I := I) (M := M) g →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  -((2 : ℝ) • gradInnerCLM (I := I) (M := M) g φ) -
    (smoothMulLp (I := I) (M := M) g
      (smoothLaplacianBundle (I := I) (M := M) g φ)).comp
      (H1ComplToLp (I := I) (M := M) g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.leibnizCompensatedSourceResidualCLMOfSmoothFactor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.leibnizCompensatedSourceResidualCLMOfSmoothFactor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.leibnizCompensatedSourceResidualCLMOfSmoothFactor ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.leibnizCompensatedSourceResidualCLMOfSmoothFactor

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma leibnizCompensatedSourceResidualCLMOfSmoothFactor_apply
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (u_h : H1Compl g) :
    leibnizCompensatedSourceResidualCLMOfSmoothFactor (I := I) (M := M) g φ u_h =
      -((2 : ℝ) • gradInnerCLM (I := I) (M := M) g φ u_h) -
        smoothMulLp (I := I) (M := M) g
          (smoothLaplacianBundle (I := I) (M := M) g φ)
          (H1ComplToLp (I := I) (M := M) g u_h) := by
  unfold leibnizCompensatedSourceResidualCLMOfSmoothFactor
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.leibnizCompensatedSourceResidualCLMOfSmoothFactor_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.leibnizCompensatedSourceResidualCLMOfSmoothFactor_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.leibnizCompensatedSourceResidualCLMOfSmoothFactor_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.leibnizCompensatedSourceResidualCLMOfSmoothFactor_apply

noncomputable def leibnizCompensatedSourceOfSmoothFactor
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (u_h : H1Compl g) (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  smoothMulLp (I := I) (M := M) g φ
      (H1ComplToLp (I := I) (M := M) g u_h -
        laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩) +
    leibnizCompensatedSourceResidualCLMOfSmoothFactor (I := I) (M := M) g φ u_h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.leibnizCompensatedSourceOfSmoothFactor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.leibnizCompensatedSourceOfSmoothFactor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.leibnizCompensatedSourceOfSmoothFactor ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.leibnizCompensatedSourceOfSmoothFactor

private noncomputable def smoothMulH1ComplInnerCLM
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (vT : SmoothScalar g) :
    H1Compl g →L[ℝ] ℝ :=
  ((innerSL ℝ : H1Compl g →L[ℝ] H1Compl g →L[ℝ] ℝ).flip
    (smoothToH1Compl (I := I) (M := M) g vT)).comp
    (smoothMulH1Compl (I := I) (M := M) g φ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulH1ComplInnerCLM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulH1ComplInnerCLM target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
@[simp] private lemma smoothMulH1ComplInnerCLM_apply
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (vT : SmoothScalar g)
    (u_h : H1Compl g) :
    smoothMulH1ComplInnerCLM (I := I) (M := M) g φ vT u_h =
      ⟪smoothMulH1Compl (I := I) (M := M) g φ u_h,
        smoothToH1Compl (I := I) (M := M) g vT⟫_ℝ := by
  unfold smoothMulH1ComplInnerCLM
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulH1ComplInnerCLM_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulH1ComplInnerCLM_apply target :: scope.openDecls } }

private noncomputable def innerSmoothMulH1ComplCLM
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (vT : SmoothScalar g) :
    H1Compl g →L[ℝ] ℝ :=
  (innerSL ℝ : H1Compl g →L[ℝ] H1Compl g →L[ℝ] ℝ).flip
    (smoothMulH1Compl (I := I) (M := M) g φ
      (smoothToH1Compl (I := I) (M := M) g vT))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.innerSmoothMulH1ComplCLM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.innerSmoothMulH1ComplCLM target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
@[simp] private lemma innerSmoothMulH1ComplCLM_apply
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (vT : SmoothScalar g)
    (u_h : H1Compl g) :
    innerSmoothMulH1ComplCLM (I := I) (M := M) g φ vT u_h =
      ⟪u_h, smoothMulH1Compl (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g vT)⟫_ℝ := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.innerSmoothMulH1ComplCLM_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.innerSmoothMulH1ComplCLM_apply target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma smoothMulH1ComplInner_smoothToH1Compl_smooth
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (uT vT : SmoothScalar g) :
    ⟪smoothMulH1Compl (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g uT),
      smoothToH1Compl (I := I) (M := M) g vT⟫_ℝ =
    @_root_.Inner.inner ℝ (SmoothScalar g) _
      (smoothScalarMulFun (I := I) (M := M) g φ uT) vT := by
  rw [smoothMulH1Compl_smoothToH1Compl]
  rw [smoothToH1Compl_apply, smoothToH1Compl_apply]
  exact UniformSpace.Completion.inner_coe _ _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulH1ComplInner_smoothToH1Compl_smooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulH1ComplInner_smoothToH1Compl_smooth target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma smoothMulH1ComplInner_smoothToH1Compl_smooth_eq_integral
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (uT vT : SmoothScalar g) :
    ⟪smoothMulH1Compl (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g uT),
      smoothToH1Compl (I := I) (M := M) g vT⟫_ℝ =
    ∫ x, ((smoothScalarMulFun (I := I) (M := M) g φ uT).toFun x -
        ΔG (I := I) g ⟨(smoothScalarMulFun (I := I) (M := M) g φ uT).toFun,
          (smoothScalarMulFun (I := I) (M := M) g φ uT).smooth⟩ x) *
        vT.toFun x
      ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [smoothMulH1ComplInner_smoothToH1Compl_smooth]
  change smoothScalarH1Inner (I := I) (M := M)
    (smoothScalarMulFun (I := I) (M := M) g φ uT) vT = _
  exact smoothScalarH1Inner_eq_integral_oneSubLap_mul
    (smoothScalarMulFun (I := I) (M := M) g φ uT) vT

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulH1ComplInner_smoothToH1Compl_smooth_eq_integral
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulH1ComplInner_smoothToH1Compl_smooth_eq_integral target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
omit [CompactSpace M] in
private lemma smoothScalarMulFun_oneSubLapClassical_pointwise_leibniz
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (uT : SmoothScalar g)
    (x : M) :
    (smoothScalarMulFun (I := I) (M := M) g φ uT).oneSubLapClassical.toFun x =
      (φ : M → ℝ) x * uT.oneSubLapClassical.toFun x -
        2 * g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g uT.toFun x) -
        uT.toFun x * ΔG (I := I) g φ x := by
  rw [SmoothScalar.oneSubLapClassical_toFun]
  have h_leibniz : ΔG (I := I) g ⟨(smoothScalarMulFun (I := I) (M := M) g φ uT).toFun,
    (smoothScalarMulFun (I := I) (M := M) g φ uT).smooth⟩ x =
    (φ : M → ℝ) x * ΔG (I := I) g ⟨uT.toFun, uT.smooth⟩ x +
      2 * g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
        (gradFun (I := I) g uT.toFun x) +
      uT.toFun x * ΔG (I := I) g φ x := by
    change ΔG (I := I) g ⟨_, φ.contMDiff.mul uT.smooth⟩ x = _
    exact Δ_g_smul_eq (I := I) (M := M) g φ.contMDiff uT.smooth x
  change (smoothScalarMulFun (I := I) (M := M) g φ uT).toFun x -
      ΔG (I := I) g ⟨(smoothScalarMulFun (I := I) (M := M) g φ uT).toFun,
        (smoothScalarMulFun (I := I) (M := M) g φ uT).smooth⟩ x =
    (φ : M → ℝ) x * uT.oneSubLapClassical.toFun x -
      2 * g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
        (gradFun (I := I) g uT.toFun x) -
      uT.toFun x * ΔG (I := I) g φ x
  rw [h_leibniz, smoothScalarMulFun_toFun,
    SmoothScalar.oneSubLapClassical_toFun]
  change ((fun y : M => (φ : M → ℝ) y * uT.toFun y) x) -
      ((φ : M → ℝ) x * ΔG (I := I) g ⟨uT.toFun, uT.smooth⟩ x +
        2 * g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g uT.toFun x) +
        uT.toFun x * ΔG (I := I) g φ x) =
    (φ : M → ℝ) x * (uT.toFun x - ΔG (I := I) g ⟨uT.toFun, uT.smooth⟩ x) -
      2 * g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
        (gradFun (I := I) g uT.toFun x) -
      uT.toFun x * ΔG (I := I) g φ x
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothScalarMulFun_oneSubLapClassical_pointwise_leibniz
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothScalarMulFun_oneSubLapClassical_pointwise_leibniz target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private theorem leibnizCompensatedSourceOfSmoothFactor_smoothToH1Compl
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (uT : SmoothScalar g) :
    leibnizCompensatedSourceOfSmoothFactor (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g uT)
        (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) uT) =
      smoothToLp (I := I) (M := M) g
        (smoothScalarMulFun (I := I) (M := M) g φ uT).oneSubLapClassical := by
  unfold leibnizCompensatedSourceOfSmoothFactor
  apply MeasureTheory.Lp.ext
  have h_oneSubLap_arg :
      H1ComplToLp (I := I) (M := M) g
          (smoothToH1Compl (I := I) (M := M) g uT) -
        laplacianOp (I := I) (M := M) g
          ⟨smoothToH1Compl (I := I) (M := M) g uT,
            smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) uT⟩ =
        smoothToLp (I := I) (M := M) g uT.oneSubLapClassical := by
    rw [H1ComplToLp_smoothToH1Compl, laplacianOp_smoothToH1Compl]
    abel
  rw [h_oneSubLap_arg]
  rw [leibnizCompensatedSourceResidualCLMOfSmoothFactor_apply, H1ComplToLp_smoothToH1Compl,
    gradInnerCLM_smoothToH1Compl]
  have h_lhs_aeEq : ((smoothMulLp (I := I) (M := M) g φ
        (smoothToLp (I := I) (M := M) g uT.oneSubLapClassical) +
      (-((2 : ℝ) • gradInnerSmooth (I := I) (M := M) g φ uT) -
        smoothMulLp (I := I) (M := M) g
          (smoothLaplacianBundle (I := I) (M := M) g φ)
          (smoothToLp (I := I) (M := M) g uT))) :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      fun x : M => (φ : M → ℝ) x * uT.oneSubLapClassical.toFun x -
        2 * g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g uT.toFun x) -
        uT.toFun x * ΔG (I := I) g φ x := by
    have h_smul_neg := MeasureTheory.Lp.coeFn_add
      (smoothMulLp (I := I) (M := M) g φ
        (smoothToLp (I := I) (M := M) g uT.oneSubLapClassical))
      (-((2 : ℝ) • gradInnerSmooth (I := I) (M := M) g φ uT) -
        smoothMulLp (I := I) (M := M) g
          (smoothLaplacianBundle (I := I) (M := M) g φ)
          (smoothToLp (I := I) (M := M) g uT))
    have h_sub := MeasureTheory.Lp.coeFn_sub
      (-((2 : ℝ) • gradInnerSmooth (I := I) (M := M) g φ uT))
      (smoothMulLp (I := I) (M := M) g
        (smoothLaplacianBundle (I := I) (M := M) g φ)
        (smoothToLp (I := I) (M := M) g uT))
    have h_neg := MeasureTheory.Lp.coeFn_neg
      ((2 : ℝ) • gradInnerSmooth (I := I) (M := M) g φ uT)
    have h_smul_two := MeasureTheory.Lp.coeFn_smul (2 : ℝ)
      (gradInnerSmooth (I := I) (M := M) g φ uT)
    have h_phi_uT_oneSubLap := smoothMulLp_apply_coeFn (I := I) (M := M) g φ
      (smoothToLp (I := I) (M := M) g uT.oneSubLapClassical)
    have h_uT_oneSubLap_coe : (smoothToLp (I := I) (M := M) g
          uT.oneSubLapClassical :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
          riemannianVolumeMeasure (I := I) (M := M) g]
        uT.oneSubLapClassical.toFun :=
      MemLp.coeFn_toLp uT.oneSubLapClassical.memLp_two
    have h_gradInnerSmooth := gradInnerSmooth_coeFn (I := I) (M := M) g φ uT
    have h_Δφ_uT := smoothMulLp_apply_coeFn (I := I) (M := M) g
      (smoothLaplacianBundle (I := I) (M := M) g φ)
      (smoothToLp (I := I) (M := M) g uT)
    have h_uT_coe : (smoothToLp (I := I) (M := M) g uT :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
          riemannianVolumeMeasure (I := I) (M := M) g] uT.toFun :=
      MemLp.coeFn_toLp uT.memLp_two
    filter_upwards [h_smul_neg, h_sub, h_neg, h_smul_two,
      h_phi_uT_oneSubLap, h_uT_oneSubLap_coe, h_gradInnerSmooth,
      h_Δφ_uT, h_uT_coe] with x h_smul_neg h_sub h_neg h_smul_two
      h_phi_uT_oneSubLap h_uT_oneSubLap_coe h_gradInnerSmooth h_Δφ_uT h_uT_coe
    rw [h_smul_neg, Pi.add_apply, h_sub, Pi.sub_apply, h_neg,
      Pi.neg_apply, h_smul_two, Pi.smul_apply, smul_eq_mul]
    rw [h_phi_uT_oneSubLap, h_uT_oneSubLap_coe,
      h_gradInnerSmooth, h_Δφ_uT, h_uT_coe]
    change (φ : M → ℝ) x * uT.oneSubLapClassical.toFun x +
        (-(2 * g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
              (gradFun (I := I) g uT.toFun x)) -
          (smoothLaplacianBundle (I := I) (M := M) g φ : M → ℝ) x *
            uT.toFun x) =
      (φ : M → ℝ) x * uT.oneSubLapClassical.toFun x -
        2 * g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g uT.toFun x) -
        uT.toFun x * ΔG (I := I) g φ x
    rw [smoothLaplacianBundle_apply]
    ring
  have h_rhs_aeEq : (smoothToLp (I := I) (M := M) g
          (smoothScalarMulFun (I := I) (M := M) g φ uT).oneSubLapClassical :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
          riemannianVolumeMeasure (I := I) (M := M) g]
        (smoothScalarMulFun (I := I) (M := M) g φ uT).oneSubLapClassical.toFun :=
    MemLp.coeFn_toLp
      (smoothScalarMulFun (I := I) (M := M) g φ uT).oneSubLapClassical.memLp_two
  refine h_lhs_aeEq.trans ?_
  refine EventuallyEq.symm ?_
  refine h_rhs_aeEq.trans ?_
  refine Filter.Eventually.of_forall ?_
  intro x
  exact smoothScalarMulFun_oneSubLapClassical_pointwise_leibniz
    (I := I) (M := M) g φ uT x

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.leibnizCompensatedSourceOfSmoothFactor_smoothToH1Compl
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.leibnizCompensatedSourceOfSmoothFactor_smoothToH1Compl target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private theorem smoothMulH1Compl_smoothToH1Compl_eq_resolvent_leibnizCompensatedSourceOfSmoothFactor
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (uT : SmoothScalar g) :
    smoothMulH1Compl (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g uT) =
      resolvent (I := I) (M := M) g
        (leibnizCompensatedSourceOfSmoothFactor (I := I) (M := M) g φ
          (smoothToH1Compl (I := I) (M := M) g uT)
          (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) uT)) := by
  rw [smoothMulH1Compl_smoothToH1Compl, leibnizCompensatedSourceOfSmoothFactor_smoothToH1Compl]
  exact (smoothToH1Compl_eq_resolvent_oneSubLap (I := I) (M := M)
    (smoothScalarMulFun (I := I) (M := M) g φ uT))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulH1Compl_smoothToH1Compl_eq_resolvent_leibnizCompensatedSourceOfSmoothFactor
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulH1Compl_smoothToH1Compl_eq_resolvent_leibnizCompensatedSourceOfSmoothFactor target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma smoothMulLp_inner_left_eq_inner_right
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (f h : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ⟪smoothMulLp (I := I) (M := M) g φ f, h⟫_ℝ =
      ⟪f, smoothMulLp (I := I) (M := M) g φ h⟫_ℝ := by
  rw [MeasureTheory.L2.inner_def (𝕜 := ℝ),
      MeasureTheory.L2.inner_def (𝕜 := ℝ)]
  refine MeasureTheory.integral_congr_ae ?_
  have h_lhs := smoothMulLp_apply_coeFn (I := I) (M := M) g φ f
  have h_rhs := smoothMulLp_apply_coeFn (I := I) (M := M) g φ h
  filter_upwards [h_lhs, h_rhs] with y h_l h_r
  rw [show @_root_.Inner.inner ℝ _ _
      (((smoothMulLp (I := I) (M := M) g φ f :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) y)
      ((h : M → ℝ) y) =
      ((h : M → ℝ) y) *
      (((smoothMulLp (I := I) (M := M) g φ f :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) y) from rfl]
  rw [show @_root_.Inner.inner ℝ _ _ ((f : M → ℝ) y)
      (((smoothMulLp (I := I) (M := M) g φ h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) y) =
      (((smoothMulLp (I := I) (M := M) g φ h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) y) *
      ((f : M → ℝ) y) from rfl]
  rw [h_l, h_r]; ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulLp_inner_left_eq_inner_right
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulLp_inner_left_eq_inner_right target :: scope.openDecls } }

private noncomputable def rewrittenRHSCLM
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (vT : SmoothScalar g) :
    H1Compl g →L[ℝ] ℝ :=
  innerSmoothMulH1ComplCLM (I := I) (M := M) g φ vT +
    ((innerSL ℝ : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ]
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ] ℝ)
      (smoothToLp (I := I) (M := M) g vT)).comp
      (leibnizCompensatedSourceResidualCLMOfSmoothFactor (I := I) (M := M) g φ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.rewrittenRHSCLM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.rewrittenRHSCLM target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
@[simp] private lemma rewrittenRHSCLM_apply
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (vT : SmoothScalar g)
    (u_h : H1Compl g) :
    rewrittenRHSCLM (I := I) (M := M) g φ vT u_h =
      ⟪u_h, smoothMulH1Compl (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g vT)⟫_ℝ +
      ⟪smoothToLp (I := I) (M := M) g vT,
        leibnizCompensatedSourceResidualCLMOfSmoothFactor (I := I) (M := M) g φ u_h⟫_ℝ := by
  unfold rewrittenRHSCLM
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.rewrittenRHSCLM_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.rewrittenRHSCLM_apply target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma smoothMulH1ComplInner_eq_rewrittenRHS_smoothToH1Compl
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (uT vT : SmoothScalar g) :
    ⟪smoothMulH1Compl (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g uT),
      smoothToH1Compl (I := I) (M := M) g vT⟫_ℝ =
    rewrittenRHSCLM (I := I) (M := M) g φ vT
      (smoothToH1Compl (I := I) (M := M) g uT) := by
  rw [rewrittenRHSCLM_apply]
  rw [smoothMulH1Compl_smoothToH1Compl_eq_resolvent_leibnizCompensatedSourceOfSmoothFactor
    (I := I) (M := M) g φ uT]
  rw [resolvent_inner_eq_lpFunctional]
  rw [H1ComplToLp_smoothToH1Compl]
  unfold leibnizCompensatedSourceOfSmoothFactor
  rw [inner_add_right]
  have h_oneSubLap_arg :
      H1ComplToLp (I := I) (M := M) g
          (smoothToH1Compl (I := I) (M := M) g uT) -
        laplacianOp (I := I) (M := M) g
          ⟨smoothToH1Compl (I := I) (M := M) g uT,
            smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) uT⟩ =
        smoothToLp (I := I) (M := M) g uT.oneSubLapClassical := by
    rw [H1ComplToLp_smoothToH1Compl, laplacianOp_smoothToH1Compl]
    abel
  rw [h_oneSubLap_arg]
  rw [← smoothMulLp_inner_left_eq_inner_right
    (I := I) (M := M) g φ (smoothToLp (I := I) (M := M) g vT)
    (smoothToLp (I := I) (M := M) g uT.oneSubLapClassical)]
  have h_lpCompat : smoothMulLp (I := I) (M := M) g φ
      (smoothToLp (I := I) (M := M) g vT) =
    H1ComplToLp (I := I) (M := M) g
      (smoothMulH1Compl (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g vT)) := by
    rw [H1ComplToLp_smoothMulH1Compl, H1ComplToLp_smoothToH1Compl]
  have h_oneSubLap_smooth :
      smoothToLp (I := I) (M := M) g uT.oneSubLapClassical =
        laplacianDomain.preimage (I := I) (M := M) g
          ⟨smoothToH1Compl (I := I) (M := M) g uT,
            smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) uT⟩ := by
    apply (resolvent_injective (I := I) (M := M) g)
    rw [resolvent_laplacianDomain_preimage_eq]
    exact (smoothToH1Compl_eq_resolvent_oneSubLap (I := I) (M := M) uT).symm
  have h_var_id :
    ⟪H1ComplToLp (I := I) (M := M) g
      (smoothMulH1Compl (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g vT)),
      laplacianDomain.preimage (I := I) (M := M) g
        ⟨smoothToH1Compl (I := I) (M := M) g uT,
          smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) uT⟩⟫_ℝ =
    ⟪smoothToH1Compl (I := I) (M := M) g uT,
      smoothMulH1Compl (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g vT)⟫_ℝ := by
    have h_resolvent :
        resolvent (I := I) (M := M) g
          (laplacianDomain.preimage (I := I) (M := M) g
            ⟨smoothToH1Compl (I := I) (M := M) g uT,
              smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) uT⟩) =
        smoothToH1Compl (I := I) (M := M) g uT :=
      resolvent_laplacianDomain_preimage_eq (I := I) (M := M) g _
    rw [show ⟪H1ComplToLp (I := I) (M := M) g
          (smoothMulH1Compl (I := I) (M := M) g φ
            (smoothToH1Compl (I := I) (M := M) g vT)),
          laplacianDomain.preimage (I := I) (M := M) g
            ⟨smoothToH1Compl (I := I) (M := M) g uT,
              smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) uT⟩⟫_ℝ =
        ⟪resolvent (I := I) (M := M) g
          (laplacianDomain.preimage (I := I) (M := M) g
            ⟨smoothToH1Compl (I := I) (M := M) g uT,
              smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) uT⟩),
          smoothMulH1Compl (I := I) (M := M) g φ
            (smoothToH1Compl (I := I) (M := M) g vT)⟫_ℝ from
      (resolvent_inner_eq_lpFunctional (I := I) (M := M) g _ _).symm]
    rw [h_resolvent]
  congr 1
  rw [h_lpCompat, h_oneSubLap_smooth]
  exact h_var_id

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulH1ComplInner_eq_rewrittenRHS_smoothToH1Compl
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulH1ComplInner_eq_rewrittenRHS_smoothToH1Compl target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private theorem smoothMulH1ComplInner_eq_rewrittenRHS
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (vT : SmoothScalar g)
    (u_h : H1Compl g) :
    ⟪smoothMulH1Compl (I := I) (M := M) g φ u_h,
      smoothToH1Compl (I := I) (M := M) g vT⟫_ℝ =
    rewrittenRHSCLM (I := I) (M := M) g φ vT u_h := by
  have h_dense := denseRange_toComplL_smoothScalar (I := I) (M := M) g
  have h_lhs_eq : ⟪smoothMulH1Compl (I := I) (M := M) g φ u_h,
      smoothToH1Compl (I := I) (M := M) g vT⟫_ℝ =
    smoothMulH1ComplInnerCLM (I := I) (M := M) g φ vT u_h :=
    (smoothMulH1ComplInnerCLM_apply (I := I) (M := M) g φ vT u_h).symm
  rw [h_lhs_eq]
  refine h_dense.induction_on (p := fun u =>
      smoothMulH1ComplInnerCLM (I := I) (M := M) g φ vT u =
        rewrittenRHSCLM (I := I) (M := M) g φ vT u) u_h ?_ ?_
  · refine isClosed_eq ?_ ?_
    · exact (smoothMulH1ComplInnerCLM (I := I) (M := M) g φ vT).continuous
    · exact (rewrittenRHSCLM (I := I) (M := M) g φ vT).continuous
  · intro uT
    show smoothMulH1ComplInnerCLM (I := I) (M := M) g φ vT
        (UniformSpace.Completion.toComplL uT) =
      rewrittenRHSCLM (I := I) (M := M) g φ vT
        (UniformSpace.Completion.toComplL uT)
    rw [smoothMulH1ComplInnerCLM_apply]
    exact smoothMulH1ComplInner_eq_rewrittenRHS_smoothToH1Compl
      (I := I) (M := M) g φ uT vT

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulH1ComplInner_eq_rewrittenRHS
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulH1ComplInner_eq_rewrittenRHS target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma rewrittenRHS_eq_original_RHS_on_laplacianDomain
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (vT : SmoothScalar g)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    rewrittenRHSCLM (I := I) (M := M) g φ vT u_h =
    ⟪H1ComplToLp (I := I) (M := M) g
        (smoothToH1Compl (I := I) (M := M) g vT),
      leibnizCompensatedSourceOfSmoothFactor (I := I) (M := M) g φ u_h hu_h⟫_ℝ := by
  rw [rewrittenRHSCLM_apply]
  rw [H1ComplToLp_smoothToH1Compl]
  unfold leibnizCompensatedSourceOfSmoothFactor
  rw [inner_add_right]
  congr 1
  have h_preimage_eq :
      H1ComplToLp (I := I) (M := M) g u_h -
        laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩ =
        laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_h⟩ := by
    rw [laplacianOp_apply]; abel
  rw [h_preimage_eq]
  rw [← smoothMulLp_inner_left_eq_inner_right
    (I := I) (M := M) g φ (smoothToLp (I := I) (M := M) g vT)
    (laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_h⟩)]
  have h_lpCompat : smoothMulLp (I := I) (M := M) g φ
      (smoothToLp (I := I) (M := M) g vT) =
    H1ComplToLp (I := I) (M := M) g
      (smoothMulH1Compl (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g vT)) := by
    rw [H1ComplToLp_smoothMulH1Compl, H1ComplToLp_smoothToH1Compl]
  rw [h_lpCompat]
  have h_resolvent_eq :
      resolvent (I := I) (M := M) g
        (laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_h⟩) = u_h :=
    resolvent_laplacianDomain_preimage_eq (I := I) (M := M) g ⟨u_h, hu_h⟩
  rw [show
    ⟪H1ComplToLp (I := I) (M := M) g
      (smoothMulH1Compl (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g vT)),
      laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_h⟩⟫_ℝ =
    ⟪resolvent (I := I) (M := M) g
      (laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_h⟩),
      smoothMulH1Compl (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g vT)⟫_ℝ from
    (resolvent_inner_eq_lpFunctional (I := I) (M := M) g _ _).symm]
  rw [h_resolvent_eq]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.rewrittenRHS_eq_original_RHS_on_laplacianDomain
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.rewrittenRHS_eq_original_RHS_on_laplacianDomain target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private theorem smoothMulH1ComplInner_eq_lpFunctional_smoothToH1Compl
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (vT : SmoothScalar g)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    ⟪smoothMulH1Compl (I := I) (M := M) g φ u_h,
      smoothToH1Compl (I := I) (M := M) g vT⟫_ℝ =
    ⟪H1ComplToLp (I := I) (M := M) g
        (smoothToH1Compl (I := I) (M := M) g vT),
      leibnizCompensatedSourceOfSmoothFactor (I := I) (M := M) g φ u_h hu_h⟫_ℝ := by
  rw [smoothMulH1ComplInner_eq_rewrittenRHS (I := I) (M := M) g φ vT u_h]
  exact rewrittenRHS_eq_original_RHS_on_laplacianDomain
    (I := I) (M := M) g φ vT hu_h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulH1ComplInner_eq_lpFunctional_smoothToH1Compl
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulH1ComplInner_eq_lpFunctional_smoothToH1Compl target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma continuous_innerSL_right
    (_g : SmoothRiemannianMetric I M) (x : H1Compl _g) :
    Continuous (fun w : H1Compl _g => ⟪w, x⟫_ℝ) := by
  exact ((innerSL ℝ : H1Compl _g →L[ℝ] H1Compl _g →L[ℝ] ℝ).flip x).continuous

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.continuous_innerSL_right
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.continuous_innerSL_right target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
theorem smoothMulH1Compl_eq_resolvent_leibnizCompensatedSourceOfSmoothFactor
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    smoothMulH1Compl (I := I) (M := M) g φ u_h =
      resolvent (I := I) (M := M) g
        (leibnizCompensatedSourceOfSmoothFactor (I := I) (M := M) g φ u_h hu_h) := by
  have h_dense := denseRange_smoothToH1Compl (I := I) (M := M) g
  refine ext_inner_left ℝ ?_
  intro w
  refine h_dense.induction_on (p := fun w =>
      ⟪w, smoothMulH1Compl (I := I) (M := M) g φ u_h⟫_ℝ =
        ⟪w, resolvent (I := I) (M := M) g
          (leibnizCompensatedSourceOfSmoothFactor (I := I) (M := M) g φ u_h hu_h)⟫_ℝ) w ?_ ?_
  · refine isClosed_eq ?_ ?_
    · exact (continuous_innerSL_right (I := I) (M := M) g
        (smoothMulH1Compl (I := I) (M := M) g φ u_h))
    · exact (continuous_innerSL_right (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (leibnizCompensatedSourceOfSmoothFactor (I := I) (M := M) g φ u_h hu_h)))
  · intro vT
    rw [real_inner_comm (smoothMulH1Compl (I := I) (M := M) g φ u_h)
      (smoothToH1Compl (I := I) (M := M) g vT)]
    rw [real_inner_comm
      (resolvent (I := I) (M := M) g
        (leibnizCompensatedSourceOfSmoothFactor (I := I) (M := M) g φ u_h hu_h))
      (smoothToH1Compl (I := I) (M := M) g vT)]
    rw [smoothMulH1ComplInner_eq_lpFunctional_smoothToH1Compl
      (I := I) (M := M) g φ vT hu_h]
    rw [resolvent_inner_eq_lpFunctional]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulH1Compl_eq_resolvent_leibnizCompensatedSourceOfSmoothFactor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulH1Compl_eq_resolvent_leibnizCompensatedSourceOfSmoothFactor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulH1Compl_eq_resolvent_leibnizCompensatedSourceOfSmoothFactor ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulH1Compl_eq_resolvent_leibnizCompensatedSourceOfSmoothFactor

omit [NeZero (Module.finrank ℝ E)] in
theorem smoothMulH1Compl_mem_laplacianDomain
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    smoothMulH1Compl (I := I) (M := M) g φ u_h ∈
      laplacianDomain (I := I) (M := M) g := by
  rw [laplacianDomain_mem_iff]
  exact ⟨leibnizCompensatedSourceOfSmoothFactor (I := I) (M := M) g φ u_h hu_h,
    smoothMulH1Compl_eq_resolvent_leibnizCompensatedSourceOfSmoothFactor (I := I) (M := M) g φ hu_h⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulH1Compl_mem_laplacianDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulH1Compl_mem_laplacianDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulH1Compl_mem_laplacianDomain ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.smoothMulH1Compl_mem_laplacianDomain

omit [NeZero (Module.finrank ℝ E)] in
theorem laplacianDomain_preimage_smoothMulH1Compl
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    laplacianDomain.preimage (I := I) (M := M) g
        ⟨smoothMulH1Compl (I := I) (M := M) g φ u_h,
          smoothMulH1Compl_mem_laplacianDomain (I := I) (M := M) g φ hu_h⟩ =
      leibnizCompensatedSourceOfSmoothFactor (I := I) (M := M) g φ u_h hu_h := by
  apply resolvent_injective (I := I) (M := M) g
  rw [resolvent_laplacianDomain_preimage_eq]
  exact smoothMulH1Compl_eq_resolvent_leibnizCompensatedSourceOfSmoothFactor
    (I := I) (M := M) g φ hu_h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.laplacianDomain_preimage_smoothMulH1Compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.laplacianDomain_preimage_smoothMulH1Compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.laplacianDomain_preimage_smoothMulH1Compl ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul.laplacianDomain_preimage_smoothMulH1Compl

end LaplacianDomainSmoothMul
end Laplacian
end Analysis
end DifferentialGeometry

end
