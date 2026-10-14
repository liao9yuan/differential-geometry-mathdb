import Submission.DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletH1Compl
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.NormSquared
import Mathlib.Analysis.Normed.Operator.Extend

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
namespace Laplacian
namespace WithBoundary
namespace Dirichlet

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.I_half
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.I_half target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpaceEuclideanSpaceRealFin_differentialGeometry : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpaceEuclideanSpaceRealFin_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpaceEuclideanSpaceRealFin_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instBorelSpaceEuclideanSpaceRealFin_differentialGeometry : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instBorelSpaceEuclideanSpaceRealFin_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instBorelSpaceEuclideanSpaceRealFin_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instBorelSpace_differentialGeometry target :: scope.openDecls } }

variable [T2Space M] [CompactSpace M]

open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Geometry.Operator.WithBoundary
open _root_.Submission.DifferentialGeometry.Integral.Measure

private noncomputable def dirichletDirectionalDerivativeSmoothScalar
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (v : SmoothScalarDirichlet q) : SmoothScalarDirichlet q where
  toFun := fun x : M => q.inner x (Y x)
    ((gradGWithBoundarySection (I := I_half n) q v.smooth v.interior_support :
      Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
        (TangentSpace (I_half n) : M → Type _)⟯) x)
  smooth := contMDiff_g_inner_of_smooth_sections (I := I_half n) q Y
    (gradGWithBoundarySection (I := I_half n) q v.smooth v.interior_support)
  interior_support := by
    refine (closure_minimal ?_ (isClosed_tsupport v.toFun)).trans v.interior_support
    intro x hx
    apply support_grad_g_with_boundary_section_subset
      (I := I_half n) q v.smooth v.interior_support
    intro hzero
    apply hx
    change q.inner x (Y x)
      ((gradGWithBoundarySection (I := I_half n) q
        v.smooth v.interior_support :
        Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
          (TangentSpace (I_half n) : M → Type _)⟯) x) = 0
    rw [hzero]
    exact (q.inner x (Y x)).map_zero

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletDirectionalDerivativeSmoothScalar
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletDirectionalDerivativeSmoothScalar target :: scope.openDecls } }

omit [T2Space M] [CompactSpace M] in
private lemma dirichletDirectionalDerivativeSmoothScalar_add
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (v w : SmoothScalarDirichlet q) :
    dirichletDirectionalDerivativeSmoothScalar q Y (v + w) =
      dirichletDirectionalDerivativeSmoothScalar q Y v +
        dirichletDirectionalDerivativeSmoothScalar q Y w := by
  apply InteriorSmoothScalar.ext
  funext x
  change q.inner x (Y x)
      ((gradGWithBoundarySection (I := I_half n) q
        (v + w).smooth (v + w).interior_support :
        Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
          (TangentSpace (I_half n) : M → Type _)⟯) x) = _
  rw [InteriorSmoothScalar.grad_g_with_boundary_section_add_apply]
  exact (q.inner x (Y x)).map_add _ _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletDirectionalDerivativeSmoothScalar_add
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletDirectionalDerivativeSmoothScalar_add target :: scope.openDecls } }

omit [T2Space M] [CompactSpace M] in
private lemma dirichletDirectionalDerivativeSmoothScalar_smul
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (c : ℝ) (v : SmoothScalarDirichlet q) :
    dirichletDirectionalDerivativeSmoothScalar q Y (c • v) =
      c • dirichletDirectionalDerivativeSmoothScalar q Y v := by
  apply InteriorSmoothScalar.ext
  funext x
  change q.inner x (Y x)
      ((gradGWithBoundarySection (I := I_half n) q
        (c • v).smooth (c • v).interior_support :
        Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
          (TangentSpace (I_half n) : M → Type _)⟯) x) = _
  rw [InteriorSmoothScalar.grad_g_with_boundary_section_smul_apply]
  exact (q.inner x (Y x)).map_smul c _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletDirectionalDerivativeSmoothScalar_smul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletDirectionalDerivativeSmoothScalar_smul target :: scope.openDecls } }

noncomputable def dirichletDirectionalDerivativeSmooth
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (v : SmoothScalarDirichlet q) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) q) :=
  smoothToLpDirichlet q (dirichletDirectionalDerivativeSmoothScalar q Y v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletDirectionalDerivativeSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletDirectionalDerivativeSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletDirectionalDerivativeSmooth ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletDirectionalDerivativeSmooth

theorem dirichletDirectionalDerivativeSmooth_coeFn
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (v : SmoothScalarDirichlet q) :
    (dirichletDirectionalDerivativeSmooth q Y v : M → ℝ) =ᵐ[
        riemannianVolumeMeasure (I := I_half n) (M := M) q]
      fun x : M => q.inner x (Y x)
        ((gradGWithBoundarySection (I := I_half n) q
          v.smooth v.interior_support :
          Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x) :=
  MemLp.coeFn_toLp
    (dirichletDirectionalDerivativeSmoothScalar q Y v).memLp_two

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletDirectionalDerivativeSmooth_coeFn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletDirectionalDerivativeSmooth_coeFn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletDirectionalDerivativeSmooth_coeFn ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletDirectionalDerivativeSmooth_coeFn

private noncomputable def dirichletDirectionalDerivativeSmoothLin
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯) :
    SmoothScalarDirichlet q →ₗ[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) q) where
  toFun := dirichletDirectionalDerivativeSmooth q Y
  map_add' v w := by
    unfold dirichletDirectionalDerivativeSmooth
    rw [dirichletDirectionalDerivativeSmoothScalar_add, map_add]
  map_smul' c v := by
    unfold dirichletDirectionalDerivativeSmooth
    rw [dirichletDirectionalDerivativeSmoothScalar_smul, map_smul]
    rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletDirectionalDerivativeSmoothLin
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletDirectionalDerivativeSmoothLin target :: scope.openDecls } }

omit [T2Space M] in
private lemma exists_dirichletDirectionalDerivativeBound
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : M, q.inner x (Y x) (Y x) ≤ B := by
  classical
  have hcont : Continuous (fun x : M => q.inner x (Y x) (Y x)) :=
    TangentBundle.continuous_g_inner_of_smooth_sections
      (I := I_half n) q Y Y
  obtain ⟨B₀, hB₀⟩ := ((isCompact_univ (X := M)).image hcont).bddAbove
  refine ⟨max B₀ 0, le_max_right _ _, fun x => ?_⟩
  exact (hB₀ ⟨x, _root_.Set.mem_univ _, rfl⟩).trans (le_max_left _ _)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_dirichletDirectionalDerivativeBound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_dirichletDirectionalDerivativeBound target :: scope.openDecls } }

private noncomputable def dirichletDirectionalDerivativeBound
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯) : ℝ :=
  Classical.choose (exists_dirichletDirectionalDerivativeBound q Y)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletDirectionalDerivativeBound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletDirectionalDerivativeBound target :: scope.openDecls } }

omit [T2Space M] in
private lemma dirichletDirectionalDerivativeBound_nonneg
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯) :
    0 ≤ dirichletDirectionalDerivativeBound q Y :=
  (Classical.choose_spec (exists_dirichletDirectionalDerivativeBound q Y)).1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletDirectionalDerivativeBound_nonneg
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletDirectionalDerivativeBound_nonneg target :: scope.openDecls } }

omit [T2Space M] in
private lemma inner_Y_self_le_dirichletDirectionalDerivativeBound
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯) (x : M) :
    q.inner x (Y x) (Y x) ≤ dirichletDirectionalDerivativeBound q Y :=
  (Classical.choose_spec (exists_dirichletDirectionalDerivativeBound q Y)).2 x

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.inner_Y_self_le_dirichletDirectionalDerivativeBound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.inner_Y_self_le_dirichletDirectionalDerivativeBound target :: scope.openDecls } }

omit [T2Space M] [CompactSpace M] in
private lemma sq_inner_Y_grad_le
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    {B : ℝ} (hY : ∀ x : M, q.inner x (Y x) (Y x) ≤ B)
    (v : SmoothScalarDirichlet q) (x : M) :
    (q.inner x (Y x)
      ((gradGWithBoundarySection (I := I_half n) q
        v.smooth v.interior_support :
        Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
          (TangentSpace (I_half n) : M → Type _)⟯) x)) ^ 2 ≤
      B * q.inner x
        ((gradGWithBoundarySection (I := I_half n) q
          v.smooth v.interior_support :
          Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x)
        ((gradGWithBoundarySection (I := I_half n) q
          v.smooth v.interior_support :
          Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x) := by
  let Z := (gradGWithBoundarySection (I := I_half n) q
    v.smooth v.interior_support :
    Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯) x
  have hY0 : 0 ≤ q.inner x (Y x) (Y x) :=
    SmoothRiemannianMetric_inner_self_nonneg q x _
  have hZ0 : 0 ≤ q.inner x Z Z :=
    SmoothRiemannianMetric_inner_self_nonneg q x _
  have hcs := abs_metric_inner_le_sqrt_metric_quadratic
    (I := I_half n) (M := M) q x (Y x) Z
  have hsq := mul_self_le_mul_self (abs_nonneg _) hcs
  have habs : |q.inner x (Y x) Z| * |q.inner x (Y x) Z| =
      (q.inner x (Y x) Z) ^ 2 := by rw [← sq, sq_abs]
  have hsqrt :
      (Real.sqrt (q.inner x (Y x) (Y x)) * Real.sqrt (q.inner x Z Z)) *
          (Real.sqrt (q.inner x (Y x) (Y x)) * Real.sqrt (q.inner x Z Z)) =
        q.inner x (Y x) (Y x) * q.inner x Z Z := by
    rw [show (Real.sqrt (q.inner x (Y x) (Y x)) * Real.sqrt (q.inner x Z Z)) *
        (Real.sqrt (q.inner x (Y x) (Y x)) * Real.sqrt (q.inner x Z Z)) =
      (Real.sqrt (q.inner x (Y x) (Y x)) *
        Real.sqrt (q.inner x (Y x) (Y x))) *
      (Real.sqrt (q.inner x Z Z) * Real.sqrt (q.inner x Z Z)) by ring]
    rw [Real.mul_self_sqrt hY0, Real.mul_self_sqrt hZ0]
  rw [habs, hsqrt] at hsq
  exact hsq.trans (mul_le_mul_of_nonneg_right (hY x) hZ0)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.sq_inner_Y_grad_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.sq_inner_Y_grad_le target :: scope.openDecls } }

private lemma norm_dirichletDirectionalDerivativeSmooth_sq_le_of_bound
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    {B : ℝ} (hB : 0 ≤ B)
    (hY : ∀ x : M, q.inner x (Y x) (Y x) ≤ B)
    (v : SmoothScalarDirichlet q) :
    ‖dirichletDirectionalDerivativeSmooth q Y v‖ ^ 2 ≤ B * ‖v‖ ^ 2 := by
  let μ := riemannianVolumeMeasure (I := I_half n) (M := M) q
  let D := dirichletDirectionalDerivativeSmoothScalar q Y v
  change ‖smoothToLpLinInterior q D‖ ^ 2 ≤ B * ‖v‖ ^ 2
  rw [InteriorSmoothScalar.norm_smoothToLp_sq]
  have hgrad :
      (∫ x, q.inner x
          ((gradGWithBoundarySection (I := I_half n) q
            v.smooth v.interior_support :
            Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
              (TangentSpace (I_half n) : M → Type _)⟯) x)
          ((gradGWithBoundarySection (I := I_half n) q
            v.smooth v.interior_support :
            Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
              (TangentSpace (I_half n) : M → Type _)⟯) x) ∂μ) ≤ ‖v‖ ^ 2 := by
    rw [InteriorSmoothScalar.norm_sq_eq_inner_self]
    unfold interiorSmoothScalarH1Inner
    linarith [v.integral_mul_self_nonneg]
  have hlhs : _root_.MeasureTheory.Integrable (fun x : M => D.toFun x * D.toFun x) μ :=
    D.integrable_mul D
  have hgrad_int : _root_.MeasureTheory.Integrable (fun x : M => q.inner x
      ((gradGWithBoundarySection (I := I_half n) q
        v.smooth v.interior_support :
        Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
          (TangentSpace (I_half n) : M → Type _)⟯) x)
      ((gradGWithBoundarySection (I := I_half n) q
        v.smooth v.interior_support :
        Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
          (TangentSpace (I_half n) : M → Type _)⟯) x)) μ :=
    v.integrable_inner_grad v
  have hmono := _root_.MeasureTheory.integral_mono_ae hlhs (hgrad_int.const_mul B)
    (Filter.Eventually.of_forall fun x => by
      change (q.inner x (Y x)
        ((gradGWithBoundarySection (I := I_half n) q
          v.smooth v.interior_support :
          Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x)) *
        (q.inner x (Y x)
        ((gradGWithBoundarySection (I := I_half n) q
          v.smooth v.interior_support :
          Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x)) ≤ _
      rw [← sq]
      exact sq_inner_Y_grad_le q Y hY v x)
  rw [_root_.MeasureTheory.integral_const_mul] at hmono
  exact hmono.trans (mul_le_mul_of_nonneg_left hgrad hB)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.norm_dirichletDirectionalDerivativeSmooth_sq_le_of_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.norm_dirichletDirectionalDerivativeSmooth_sq_le_of_bound target :: scope.openDecls } }

private lemma norm_dirichletDirectionalDerivativeSmooth_le_of_bound
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    {B : ℝ} (hB : 0 ≤ B)
    (hY : ∀ x : M, q.inner x (Y x) (Y x) ≤ B)
    (v : SmoothScalarDirichlet q) :
    ‖dirichletDirectionalDerivativeSmooth q Y v‖ ≤ Real.sqrt B * ‖v‖ := by
  apply abs_le_of_sq_le_sq' _ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) |>.2
  rw [mul_pow, Real.sq_sqrt hB]
  exact norm_dirichletDirectionalDerivativeSmooth_sq_le_of_bound q Y hB hY v

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.norm_dirichletDirectionalDerivativeSmooth_le_of_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.norm_dirichletDirectionalDerivativeSmooth_le_of_bound target :: scope.openDecls } }

private noncomputable def dirichletDirectionalDerivativeOnSmooth
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯) :
    SmoothScalarDirichlet q →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) q) :=
  (dirichletDirectionalDerivativeSmoothLin q Y).mkContinuous
    (Real.sqrt (dirichletDirectionalDerivativeBound q Y))
    (norm_dirichletDirectionalDerivativeSmooth_le_of_bound q Y
      (dirichletDirectionalDerivativeBound_nonneg q Y)
      (inner_Y_self_le_dirichletDirectionalDerivativeBound q Y))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletDirectionalDerivativeOnSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletDirectionalDerivativeOnSmooth target :: scope.openDecls } }

noncomputable def dirichletDirectionalDerivativeCLM
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯) :
    H1ComplDirichlet q →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) q) :=
  ContinuousLinearMap.extend (dirichletDirectionalDerivativeOnSmooth q Y)
    (UniformSpace.Completion.toComplL :
      SmoothScalarDirichlet q →L[ℝ] H1ComplDirichlet q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletDirectionalDerivativeCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletDirectionalDerivativeCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletDirectionalDerivativeCLM ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletDirectionalDerivativeCLM

theorem dirichletDirectionalDerivativeCLM_smoothToH1ComplDirichlet
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (v : SmoothScalarDirichlet q) :
    dirichletDirectionalDerivativeCLM q Y
        (smoothToH1ComplDirichlet q v) =
      dirichletDirectionalDerivativeSmooth q Y v := by
  unfold dirichletDirectionalDerivativeCLM
  exact ContinuousLinearMap.extend_eq
    (dirichletDirectionalDerivativeOnSmooth q Y)
    (denseRange_smoothToH1ComplDirichlet q)
    (UniformSpace.Completion.isUniformInducing_coe (SmoothScalarDirichlet q)) v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletDirectionalDerivativeCLM_smoothToH1ComplDirichlet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletDirectionalDerivativeCLM_smoothToH1ComplDirichlet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletDirectionalDerivativeCLM_smoothToH1ComplDirichlet ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletDirectionalDerivativeCLM_smoothToH1ComplDirichlet

theorem norm_dirichletDirectionalDerivativeCLM_le
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    {B : ℝ} (hB : 0 ≤ B)
    (hY : ∀ x : M, q.inner x (Y x) (Y x) ≤ B) :
    ‖dirichletDirectionalDerivativeCLM q Y‖ ≤ Real.sqrt B := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro u
  refine (denseRange_smoothToH1ComplDirichlet q).induction_on u
    (isClosed_le (dirichletDirectionalDerivativeCLM q Y).continuous.norm
      (continuous_const.mul continuous_norm)) ?_
  intro v
  rw [dirichletDirectionalDerivativeCLM_smoothToH1ComplDirichlet]
  have hnorm : ‖smoothToH1ComplDirichlet q v‖ = ‖v‖ := by
    change ‖(v : UniformSpace.Completion (SmoothScalarDirichlet q))‖ = ‖v‖
    exact UniformSpace.Completion.norm_coe v
  rw [hnorm]
  exact norm_dirichletDirectionalDerivativeSmooth_le_of_bound q Y hB hY v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.norm_dirichletDirectionalDerivativeCLM_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.norm_dirichletDirectionalDerivativeCLM_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.norm_dirichletDirectionalDerivativeCLM_le ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.norm_dirichletDirectionalDerivativeCLM_le

end Dirichlet
end WithBoundary
end Laplacian
end Analysis
end DifferentialGeometry

end
