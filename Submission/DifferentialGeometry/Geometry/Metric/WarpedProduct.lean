import Submission.DifferentialGeometry.Geometry.Metric.Product
import Submission.DifferentialGeometry.Geometry.Metric.Scaling

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]

private def warpedInner
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N) (f : M → ℝ)
    (x : M × N) : TangentSpace (I.prod J) x →L[ℝ]
      TangentSpace (I.prod J) x →L[ℝ] ℝ :=
  localPullInner g Prod.fst x + f x.1 ^ 2 • localPullInner h Prod.snd x

run_cmd do
  let target := ``Submission.DifferentialGeometry.warpedInner
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.warpedInner target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [T2Space M] [T2Space N] in
private theorem warpedInner_apply
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N) (f : M → ℝ)
    (x : M × N) (v w : TangentSpace (I.prod J) x) :
    warpedInner g h f x v w =
      g.inner x.1 v.1 w.1 + f x.1 ^ 2 * h.inner x.2 v.2 w.2 := by
  simp only [warpedInner, add_apply, smul_apply, smul_eq_mul, localPullInner_apply,
    mfderiv_fst, mfderiv_snd]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.warpedInner_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.warpedInner_apply target :: scope.openDecls } }

private theorem warpedInner_eq_product_inner
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N) (f : M → ℝ)
    (hf : ∀ x, 0 < f x) (x : M × N) :
    warpedInner g h f x =
      (g.prod (scaleMetric (f x.1 ^ 2) (sq_pos_of_pos (hf x.1)) h)).inner x := by
  ext v w
  rw [warpedInner_apply, SmoothRiemannianMetric.prod_inner]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.warpedInner_eq_product_inner
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.warpedInner_eq_product_inner target :: scope.openDecls } }

def SmoothRiemannianMetric.warpedProduct
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N) (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hpos : ∀ x, 0 < f x) :
    SmoothRiemannianMetric (I.prod J) (M × N) where
  inner := warpedInner g h f
  symm x := by
    rw [warpedInner_eq_product_inner g h f hpos x]
    exact (g.prod (scaleMetric (f x.1 ^ 2) (sq_pos_of_pos (hpos x.1)) h)).symm x
  pos x := by
    rw [warpedInner_eq_product_inner g h f hpos x]
    exact (g.prod (scaleMetric (f x.1 ^ 2) (sq_pos_of_pos (hpos x.1)) h)).pos x
  isVonNBounded x := by
    simp only [warpedInner_eq_product_inner g h f hpos x]
    exact (g.prod (scaleMetric (f x.1 ^ 2) (sq_pos_of_pos (hpos x.1)) h)).isVonNBounded x
  contMDiff :=
    (contMDiff_localPullInner g Prod.fst contMDiff_fst).add_section
      (((hf.comp contMDiff_fst).pow 2).smul_section
        (contMDiff_localPullInner h Prod.snd contMDiff_snd))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SmoothRiemannianMetric.warpedProduct then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SmoothRiemannianMetric.warpedProduct"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SmoothRiemannianMetric.warpedProduct ``Submission.DifferentialGeometry.SmoothRiemannianMetric.warpedProduct

@[simp]
theorem SmoothRiemannianMetric.warpedProduct_inner
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N) (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hpos : ∀ x, 0 < f x)
    (x : M × N) (v w : TangentSpace (I.prod J) x) :
    (g.warpedProduct h f hf hpos).inner x v w =
      g.inner x.1 v.1 w.1 + f x.1 ^ 2 * h.inner x.2 v.2 w.2 :=
  warpedInner_apply g h f x v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SmoothRiemannianMetric.warpedProduct_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SmoothRiemannianMetric.warpedProduct_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SmoothRiemannianMetric.warpedProduct_inner ``Submission.DifferentialGeometry.SmoothRiemannianMetric.warpedProduct_inner

theorem SmoothRiemannianMetric.warpedProduct_const
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (c : ℝ) (hc : 0 < c) :
    g.warpedProduct h (fun _ => c) contMDiff_const (fun _ => hc) =
      g.prod (scaleMetric (c ^ 2) (sq_pos_of_pos hc) h) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [SmoothRiemannianMetric.warpedProduct_inner, SmoothRiemannianMetric.prod_inner]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SmoothRiemannianMetric.warpedProduct_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SmoothRiemannianMetric.warpedProduct_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SmoothRiemannianMetric.warpedProduct_const ``Submission.DifferentialGeometry.SmoothRiemannianMetric.warpedProduct_const

@[simp]
theorem SmoothRiemannianMetric.warpedProduct_one
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N) :
    g.warpedProduct h (fun _ => 1) contMDiff_const (fun _ => zero_lt_one) =
      g.prod h := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  simp only [SmoothRiemannianMetric.warpedProduct_inner,
    SmoothRiemannianMetric.prod_inner, one_pow, one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SmoothRiemannianMetric.warpedProduct_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SmoothRiemannianMetric.warpedProduct_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SmoothRiemannianMetric.warpedProduct_one ``Submission.DifferentialGeometry.SmoothRiemannianMetric.warpedProduct_one

end DifferentialGeometry
