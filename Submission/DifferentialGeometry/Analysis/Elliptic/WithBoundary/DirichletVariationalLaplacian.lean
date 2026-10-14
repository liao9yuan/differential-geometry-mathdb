import Submission.DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletDensity

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

variable [T2Space M] [CompactSpace M]

open _root_.Submission.DifferentialGeometry.Integral.Measure

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

def dirichletLaplacianDomain
    (g : SmoothRiemannianMetric (I_half n) M) :
    Submodule ℝ (H1ComplDirichlet g) :=
  LinearMap.range (resolventDirichlet g).toLinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLaplacianDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLaplacianDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLaplacianDomain ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLaplacianDomain

lemma dirichletLaplacianDomain_mem_iff
    (g : SmoothRiemannianMetric (I_half n) M) {u : H1ComplDirichlet g} :
    u ∈ dirichletLaplacianDomain g ↔
      ∃ f : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g),
        u = resolventDirichlet g f := by
  unfold dirichletLaplacianDomain
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f, hf.symm⟩
  · rintro ⟨f, hf⟩
    exact ⟨f, hf.symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLaplacianDomain_mem_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLaplacianDomain_mem_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLaplacianDomain_mem_iff ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLaplacianDomain_mem_iff

def dirichletResolventEquiv
    (g : SmoothRiemannianMetric (I_half n) M) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) ≃ₗ[ℝ]
      dirichletLaplacianDomain g :=
  LinearEquiv.ofInjective (resolventDirichlet g).toLinearMap
    (resolventDirichlet_injective g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletResolventEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletResolventEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletResolventEquiv ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletResolventEquiv

@[simp] theorem dirichletResolventEquiv_apply
    (g : SmoothRiemannianMetric (I_half n) M)
    (f : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)) :
    (dirichletResolventEquiv g f : H1ComplDirichlet g) =
      resolventDirichlet g f := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletResolventEquiv_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletResolventEquiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletResolventEquiv_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletResolventEquiv_apply

@[simp] theorem resolventDirichlet_dirichletResolventEquiv_symm
    (g : SmoothRiemannianMetric (I_half n) M)
    (u : dirichletLaplacianDomain g) :
    resolventDirichlet g ((dirichletResolventEquiv g).symm u) =
      (u : H1ComplDirichlet g) :=
  LinearEquiv.ofInjective_symm_apply _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.resolventDirichlet_dirichletResolventEquiv_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.resolventDirichlet_dirichletResolventEquiv_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.resolventDirichlet_dirichletResolventEquiv_symm ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.resolventDirichlet_dirichletResolventEquiv_symm

def dirichletLaplacian
    (g : SmoothRiemannianMetric (I_half n) M) :
    dirichletLaplacianDomain g →ₗ[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
  ((H1ComplDirichletToLp g).toLinearMap.comp
    (dirichletLaplacianDomain g).subtype) -
  (dirichletResolventEquiv g).symm.toLinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLaplacian then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLaplacian"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLaplacian ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLaplacian

@[simp] lemma dirichletLaplacian_apply
    (g : SmoothRiemannianMetric (I_half n) M)
    (u : dirichletLaplacianDomain g) :
    dirichletLaplacian g u =
      H1ComplDirichletToLp g (u : H1ComplDirichlet g) -
        (dirichletResolventEquiv g).symm u := by
  unfold dirichletLaplacian
  rw [LinearMap.sub_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLaplacian_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLaplacian_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLaplacian_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLaplacian_apply

theorem dirichletLaplacian_resolvent
    (g : SmoothRiemannianMetric (I_half n) M)
    (f : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)) :
    dirichletLaplacian g
        ⟨resolventDirichlet g f,
          (dirichletLaplacianDomain_mem_iff g).mpr ⟨f, rfl⟩⟩ =
      H1ComplDirichletToLp g (resolventDirichlet g f) - f := by
  rw [dirichletLaplacian_apply]
  have hpreimage :
      (dirichletResolventEquiv g).symm
          ⟨resolventDirichlet g f,
            (dirichletLaplacianDomain_mem_iff g).mpr ⟨f, rfl⟩⟩ = f := by
    apply resolventDirichlet_injective g
    rw [resolventDirichlet_dirichletResolventEquiv_symm]
  rw [hpreimage]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLaplacian_resolvent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLaplacian_resolvent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLaplacian_resolvent ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLaplacian_resolvent

lemma smoothToH1ComplDirichlet_mem_dirichletLaplacianDomain
    {g : SmoothRiemannianMetric (I_half n) M}
    (u : SmoothScalarDirichlet g) :
    smoothToH1ComplDirichlet g u ∈ dirichletLaplacianDomain g := by
  rw [dirichletLaplacianDomain_mem_iff]
  exact ⟨u.oneSubLapClassicalLp,
    smoothToH1ComplDirichlet_eq_resolventDirichlet_oneSubLap u⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.smoothToH1ComplDirichlet_mem_dirichletLaplacianDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.smoothToH1ComplDirichlet_mem_dirichletLaplacianDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.smoothToH1ComplDirichlet_mem_dirichletLaplacianDomain ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.smoothToH1ComplDirichlet_mem_dirichletLaplacianDomain

theorem dirichletLaplacian_smoothToH1ComplDirichlet
    {g : SmoothRiemannianMetric (I_half n) M}
    (u : SmoothScalarDirichlet g) :
    dirichletLaplacian g
        ⟨smoothToH1ComplDirichlet g u,
          smoothToH1ComplDirichlet_mem_dirichletLaplacianDomain u⟩ =
      smoothToLpDirichlet g u - u.oneSubLapClassicalLp := by
  rw [show (⟨smoothToH1ComplDirichlet g u,
        smoothToH1ComplDirichlet_mem_dirichletLaplacianDomain u⟩ :
        dirichletLaplacianDomain g) =
      ⟨resolventDirichlet g u.oneSubLapClassicalLp,
        (dirichletLaplacianDomain_mem_iff g).mpr
          ⟨u.oneSubLapClassicalLp, rfl⟩⟩ from ?_]
  · rw [dirichletLaplacian_resolvent]
    rw [← smoothToH1ComplDirichlet_eq_resolventDirichlet_oneSubLap u]
    rw [H1ComplDirichletToLp_smoothToH1ComplDirichlet]
  · apply Subtype.ext
    exact smoothToH1ComplDirichlet_eq_resolventDirichlet_oneSubLap u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLaplacian_smoothToH1ComplDirichlet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLaplacian_smoothToH1ComplDirichlet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLaplacian_smoothToH1ComplDirichlet ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLaplacian_smoothToH1ComplDirichlet

private lemma h1Inner_eq_lpInner_with_dirichletPreimage
    (g : SmoothRiemannianMetric (I_half n) M)
    (u v : dirichletLaplacianDomain g) :
    ⟪(u : H1ComplDirichlet g), (v : H1ComplDirichlet g)⟫_ℝ =
      ⟪H1ComplDirichletToLp g (v : H1ComplDirichlet g),
        (dirichletResolventEquiv g).symm u⟫_ℝ := by
  have hu : (u : H1ComplDirichlet g) =
      resolventDirichlet g ((dirichletResolventEquiv g).symm u) :=
    (resolventDirichlet_dirichletResolventEquiv_symm g u).symm
  rw [hu]
  exact resolventDirichlet_inner_eq_lpFunctional g
    ((dirichletResolventEquiv g).symm u) (v : H1ComplDirichlet g)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.h1Inner_eq_lpInner_with_dirichletPreimage
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.h1Inner_eq_lpInner_with_dirichletPreimage target :: scope.openDecls } }

private lemma lpInner_dirichletPreimage_swap
    (g : SmoothRiemannianMetric (I_half n) M)
    (u v : dirichletLaplacianDomain g) :
    ⟪H1ComplDirichletToLp g (v : H1ComplDirichlet g),
        (dirichletResolventEquiv g).symm u⟫_ℝ =
      ⟪H1ComplDirichletToLp g (u : H1ComplDirichlet g),
        (dirichletResolventEquiv g).symm v⟫_ℝ := by
  rw [← h1Inner_eq_lpInner_with_dirichletPreimage g u v]
  rw [← h1Inner_eq_lpInner_with_dirichletPreimage g v u]
  exact real_inner_comm _ _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.lpInner_dirichletPreimage_swap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.lpInner_dirichletPreimage_swap target :: scope.openDecls } }

theorem dirichletLaplacian_symmetric
    (g : SmoothRiemannianMetric (I_half n) M)
    (u v : dirichletLaplacianDomain g) :
    ⟪H1ComplDirichletToLp g (u : H1ComplDirichlet g),
        dirichletLaplacian g v⟫_ℝ =
      ⟪dirichletLaplacian g u,
        H1ComplDirichletToLp g (v : H1ComplDirichlet g)⟫_ℝ := by
  rw [dirichletLaplacian_apply, dirichletLaplacian_apply]
  rw [inner_sub_right, inner_sub_left]
  have hswap := lpInner_dirichletPreimage_swap g v u
  have hswap' :
      ⟪H1ComplDirichletToLp g (u : H1ComplDirichlet g),
          (dirichletResolventEquiv g).symm v⟫_ℝ =
        ⟪(dirichletResolventEquiv g).symm u,
          H1ComplDirichletToLp g (v : H1ComplDirichlet g)⟫_ℝ := by
    rw [hswap, real_inner_comm]
  linarith [hswap']

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLaplacian_symmetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLaplacian_symmetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLaplacian_symmetric ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLaplacian_symmetric

theorem inner_resolventDirichlet_oneSubLap
    (g : SmoothRiemannianMetric (I_half n) M)
    (f : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))
    (φ : SmoothScalarDirichlet g) :
    ⟪H1ComplDirichletToLp g (resolventDirichlet g f), φ.oneSubLapClassicalLp⟫_ℝ =
      ⟪f, smoothToLpDirichlet g φ⟫_ℝ := by
  rw [← resolventDirichlet_inner_eq_lpFunctional g φ.oneSubLapClassicalLp,
    ← smoothToH1ComplDirichlet_eq_resolventDirichlet_oneSubLap φ, real_inner_comm,
    resolventDirichlet_inner_eq_lpFunctional,
    H1ComplDirichletToLp_smoothToH1ComplDirichlet, real_inner_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.inner_resolventDirichlet_oneSubLap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.inner_resolventDirichlet_oneSubLap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.inner_resolventDirichlet_oneSubLap ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.inner_resolventDirichlet_oneSubLap

theorem dirichletLaplacian_inner_smooth
    (g : SmoothRiemannianMetric (I_half n) M)
    (u : dirichletLaplacianDomain g) (φ : SmoothScalarDirichlet g) :
    ⟪dirichletLaplacian g u, smoothToLpDirichlet g φ⟫_ℝ =
      ⟪H1ComplDirichletToLp g u,
        smoothToLpDirichlet g φ - φ.oneSubLapClassicalLp⟫_ℝ := by
  let v : dirichletLaplacianDomain g :=
    ⟨smoothToH1ComplDirichlet g φ,
      smoothToH1ComplDirichlet_mem_dirichletLaplacianDomain φ⟩
  have h := dirichletLaplacian_symmetric g u v
  rw [show H1ComplDirichletToLp g (v : H1ComplDirichlet g) =
      smoothToLpDirichlet g φ from
        H1ComplDirichletToLp_smoothToH1ComplDirichlet g φ,
    show dirichletLaplacian g v =
      smoothToLpDirichlet g φ - φ.oneSubLapClassicalLp from
        dirichletLaplacian_smoothToH1ComplDirichlet φ] at h
  exact h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLaplacian_inner_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLaplacian_inner_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLaplacian_inner_smooth ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLaplacian_inner_smooth

theorem integral_resolventDirichlet_oneSubLap
    (g : SmoothRiemannianMetric (I_half n) M)
    (f : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))
    (φ : SmoothScalarDirichlet g) :
    (∫ x, H1ComplDirichletToLp g (resolventDirichlet g f) x *
        (φ.toFun x - DifferentialGeometry.Geometry.Operator.WithBoundary.ΔGWithBoundary
          (I := I_half n) g φ.smooth φ.interior_support x)
      ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) =
      ∫ x, f x * φ.toFun x
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
  have h := inner_resolventDirichlet_oneSubLap g f φ
  simp only [L2.inner_def, RCLike.inner_apply, conj_trivial] at h
  have hφ := MemLp.coeFn_toLp φ.memLp_two
  have hΔφ := MemLp.coeFn_toLp φ.oneSubLap_memLp
  calc
    _ = ∫ x, φ.oneSubLapClassicalLp x *
        H1ComplDirichletToLp g (resolventDirichlet g f) x
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
      apply _root_.MeasureTheory.integral_congr_ae
      filter_upwards [hΔφ] with x hx
      change (φ.oneSubLapClassicalLp : M → ℝ) x = _ at hx
      rw [hx, mul_comm]
    _ = ∫ x, smoothToLpDirichlet g φ x * f x
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) := h
    _ = _ := by
      apply _root_.MeasureTheory.integral_congr_ae
      filter_upwards [hφ] with x hx
      change smoothToLpDirichlet g φ x = φ.toFun x at hx
      rw [hx, mul_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.integral_resolventDirichlet_oneSubLap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.integral_resolventDirichlet_oneSubLap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.integral_resolventDirichlet_oneSubLap ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.integral_resolventDirichlet_oneSubLap

theorem integral_dirichletLaplacian_mul_smooth
    (g : SmoothRiemannianMetric (I_half n) M)
    (u : dirichletLaplacianDomain g) (φ : SmoothScalarDirichlet g) :
    (∫ x, dirichletLaplacian g u x * φ.toFun x
      ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) =
      ∫ x, H1ComplDirichletToLp g u x *
        DifferentialGeometry.Geometry.Operator.WithBoundary.ΔGWithBoundary
          (I := I_half n) g φ.smooth φ.interior_support x
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
  have h := dirichletLaplacian_inner_smooth g u φ
  simp only [L2.inner_def, RCLike.inner_apply, conj_trivial] at h
  have hφ := MemLp.coeFn_toLp φ.memLp_two
  have hΔφ := MemLp.coeFn_toLp φ.oneSubLap_memLp
  calc
    _ = ∫ x, smoothToLpDirichlet g φ x * dirichletLaplacian g u x
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
      apply _root_.MeasureTheory.integral_congr_ae
      filter_upwards [hφ] with x hx
      change smoothToLpDirichlet g φ x = φ.toFun x at hx
      rw [hx, mul_comm]
    _ = ∫ x, (smoothToLpDirichlet g φ - φ.oneSubLapClassicalLp) x *
        H1ComplDirichletToLp g u x
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) := h
    _ = _ := by
      apply _root_.MeasureTheory.integral_congr_ae
      filter_upwards [Lp.coeFn_sub (smoothToLpDirichlet g φ) φ.oneSubLapClassicalLp,
        hφ, hΔφ] with x hsub hx hΔx
      change smoothToLpDirichlet g φ x = φ.toFun x at hx
      change (φ.oneSubLapClassicalLp : M → ℝ) x = _ at hΔx
      rw [hsub, Pi.sub_apply, hx, hΔx]
      ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.integral_dirichletLaplacian_mul_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.integral_dirichletLaplacian_mul_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.integral_dirichletLaplacian_mul_smooth ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.integral_dirichletLaplacian_mul_smooth

end Dirichlet
end WithBoundary
end Laplacian
end Analysis
end DifferentialGeometry

end

noncomputable section

open _root_.Manifold _root_.MeasureTheory
open scoped _root_.ContDiff _root_.ENNReal _root_.InnerProductSpace _root_.Manifold _root_.RealInnerProductSpace _root_.Topology

namespace DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

open _root_.Submission.DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

theorem dirichletLaplacian_inner_h1ComplDirichlet
    (q : SmoothRiemannianMetric I_hs M)
    (u : dirichletLaplacianDomain q) (v : H1ComplDirichlet q) :
    ⟪dirichletLaplacian q u, H1ComplDirichletToLp q v⟫_ℝ =
      ⟪H1ComplDirichletToLp q (u : H1ComplDirichlet q), H1ComplDirichletToLp q v⟫_ℝ -
        ⟪(u : H1ComplDirichlet q), v⟫_ℝ := by
  rw [dirichletLaplacian_apply, inner_sub_left]
  have hu := resolventDirichlet_inner_eq_lpFunctional q
    ((dirichletResolventEquiv q).symm u) v
  rw [resolventDirichlet_dirichletResolventEquiv_symm] at hu
  rw [hu, real_inner_comm ((dirichletResolventEquiv q).symm u)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLaplacian_inner_h1ComplDirichlet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLaplacian_inner_h1ComplDirichlet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLaplacian_inner_h1ComplDirichlet ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLaplacian_inner_h1ComplDirichlet

end DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

end
