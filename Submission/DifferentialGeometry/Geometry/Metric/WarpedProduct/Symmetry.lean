import Submission.DifferentialGeometry.Geometry.Metric.Product.VerticalCoefficient
import Submission.DifferentialGeometry.Geometry.Metric.WarpedProduct
import Submission.DifferentialGeometry.Geometry.Metric.ProductSlice
import Submission.DifferentialGeometry.Geometry.Metric.Euclidean
import Submission.DifferentialGeometry.Topology.Manifold.EuclideanBoundaryCoordinates
import Submission.DifferentialGeometry.Geometry.Metric.Pullback.Cross

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

private theorem bilinear_prod_eq_of_reflection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : (E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ)
    (hreflect : ∀ v w : E × ℝ, B (v.1, -v.2) (w.1, -w.2) = B v w)
    (v w : E × ℝ) :
    B v w = B (v.1, 0) (w.1, 0) + v.2 * w.2 * B (0, 1) (0, 1) := by
  have hleft (u : E) : B (u, 0) (0, 1) = 0 := by
    have h := hreflect (u, 0) (0, 1)
    change B (u, -(0 : ℝ)) ((0 : E), -(1 : ℝ)) = B (u, 0) (0, 1) at h
    rw [neg_zero] at h
    have hneg : ((0 : E), -(1 : ℝ)) = -((0 : E), (1 : ℝ)) := by simp
    rw [hneg, map_neg] at h
    linarith
  have hright (u : E) : B (0, 1) (u, 0) = 0 := by
    have h := hreflect (0, 1) (u, 0)
    change B ((0 : E), -(1 : ℝ)) (u, -(0 : ℝ)) = B (0, 1) (u, 0) at h
    rw [neg_zero] at h
    have hneg : ((0 : E), -(1 : ℝ)) = -((0 : E), (1 : ℝ)) := by simp
    rw [hneg, map_neg, neg_apply] at h
    linarith
  have hv : v = (v.1, 0) + v.2 • ((0 : E), (1 : ℝ)) := by
    ext <;> simp
  have hw : w = (w.1, 0) + w.2 • ((0 : E), (1 : ℝ)) := by
    ext <;> simp
  calc
    B v w = B ((v.1, 0) + v.2 • ((0 : E), (1 : ℝ)))
        ((w.1, 0) + w.2 • ((0 : E), (1 : ℝ))) := congrArg₂ (fun a b => B a b) hv hw
    _ = _ := by
      simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul, hleft, hright]
      ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.bilinear_prod_eq_of_reflection
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.bilinear_prod_eq_of_reflection target :: scope.openDecls } }

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem SmoothRiemannianMetric.inner_eq_sliceFst_add_vertical_of_translation_reflection
    (G : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))
    (htranslate : ∀ (x : M) (r c : ℝ) (v w : E × ℝ),
      G.inner (x, r + c) v w = G.inner (x, r) v w)
    (hreflect : ∀ (x : M) (r : ℝ) (v w : E × ℝ),
      G.inner (x, -r) (v.1, -v.2) (w.1, -w.2) = G.inner (x, r) v w)
    (x : M) (r : ℝ) (v w : E × ℝ) :
    G.inner (x, r) v w = (G.sliceFst 0).inner x v.1 w.1 +
      v.2 * w.2 * G.inner (x, 0) (0, 1) (0, 1) := by
  have hzero (v w : E × ℝ) : G.inner (x, r) v w = G.inner (x, 0) v w := by
    have h := htranslate x 0 r v w
    let B : M × ℝ → (E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ := fun p => G.inner p
    change B (x, 0 + r) v w = B (x, 0) v w at h
    rw [zero_add] at h
    exact h
  change G.inner (x, r) (v : E × ℝ) (w : E × ℝ) = _
  rw [hzero v w]
  change G.inner (x, 0) v w = G.inner (x, 0) (v.1, 0) (w.1, 0) + _
  exact bilinear_prod_eq_of_reflection (G.inner (x, 0))
    (fun v w => by
      have h := hreflect x 0 v w
      let B : M × ℝ → (E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ := fun p => G.inner p
      change B (x, -0) (v.1, -v.2) (w.1, -w.2) = B (x, 0) v w at h
      rw [neg_zero] at h
      exact h) v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SmoothRiemannianMetric.inner_eq_sliceFst_add_vertical_of_translation_reflection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SmoothRiemannianMetric.inner_eq_sliceFst_add_vertical_of_translation_reflection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SmoothRiemannianMetric.inner_eq_sliceFst_add_vertical_of_translation_reflection ``Submission.DifferentialGeometry.SmoothRiemannianMetric.inner_eq_sliceFst_add_vertical_of_translation_reflection

theorem SmoothRiemannianMetric.eq_warpedProduct_of_translation_reflection
    (G : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))
    (htranslate : ∀ (x : M) (r c : ℝ) (v w : E × ℝ),
      G.inner (x, r + c) v w = G.inner (x, r) v w)
    (hreflect : ∀ (x : M) (r : ℝ) (v w : E × ℝ),
      G.inner (x, -r) (v.1, -v.2) (w.1, -w.2) = G.inner (x, r) v w) :
    G = (G.sliceFst 0).warpedProduct (euclideanMetric (E := ℝ))
      (fun x => Real.sqrt (G.inner (x, 0) (0, 1) (0, 1)))
      (G.contMDiff_sqrt_vertical_inner 0) (fun x => G.sqrt_vertical_inner_pos x 0) := by
  apply SmoothRiemannianMetric.ext_inner
  rintro ⟨x, r⟩ v w
  change E × ℝ at v w
  erw [G.inner_eq_sliceFst_add_vertical_of_translation_reflection htranslate hreflect,
    SmoothRiemannianMetric.warpedProduct_inner,
    Real.sq_sqrt (G.vertical_inner_pos x 0).le]
  change _ = _ + _ * (w.2 * v.2)
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SmoothRiemannianMetric.eq_warpedProduct_of_translation_reflection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SmoothRiemannianMetric.eq_warpedProduct_of_translation_reflection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SmoothRiemannianMetric.eq_warpedProduct_of_translation_reflection ``Submission.DifferentialGeometry.SmoothRiemannianMetric.eq_warpedProduct_of_translation_reflection

end DifferentialGeometry

end

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] in
private theorem mfderiv_prod_translation (c : ℝ) (p : M × ℝ) (v : E × ℝ) :
    mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ))
      (fun z : M × ℝ => (z.1, z.2 + c)) p v = v := by
  have hadd : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
      (fun z : M × ℝ => z.2 + c) p := mdifferentiableAt_snd.add mdifferentiableAt_const
  erw [mfderiv_prodMk mdifferentiableAt_fst hadd]
  have hd : mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
      (fun z : M × ℝ => z.2 + c) p =
        ContinuousLinearMap.snd ℝ (TangentSpace I p.1) ℝ := by
    change mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
      (Prod.snd + fun _ : M × ℝ => c) p = _
    erw [mfderiv_add mdifferentiableAt_snd mdifferentiableAt_const, mfderiv_const,
      add_zero, mfderiv_snd]
    rfl
  erw [hd, mfderiv_fst]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.mfderiv_prod_translation
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.mfderiv_prod_translation target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] in
private theorem mfderiv_prod_reflection (p : M × ℝ) (v : E × ℝ) :
    mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ))
      (fun z : M × ℝ => (z.1, -z.2)) p v = (v.1, -v.2) := by
  erw [mfderiv_prodMk mdifferentiableAt_fst mdifferentiableAt_snd.neg]
  change ((mfderiv (I.prod 𝓘(ℝ, ℝ)) I Prod.fst p).prod
    (mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (-Prod.snd) p)) v = _
  erw [mfderiv_neg, mfderiv_snd, mfderiv_fst]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.mfderiv_prod_reflection
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.mfderiv_prod_reflection target :: scope.openDecls } }

theorem SmoothRiemannianMetric.eq_warpedProduct_of_pullback_translation_reflection
    (G : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))
    (htranslate : ∀ c : ℝ,
      Diffeomorph.pullbackMetricCross G
        ((Diffeomorph.refl I M ∞).prodCongr (Topology.translateDiffeomorph c)) = G)
    (hreflect : Diffeomorph.pullbackMetricCross G
      ((Diffeomorph.refl I M ∞).prodCongr
        (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ).toContinuousLinearEquiv.toDiffeomorph) = G) :
    G = (G.sliceFst 0).warpedProduct (euclideanMetric (E := ℝ))
      (fun x => Real.sqrt (G.inner (x, 0) (0, 1) (0, 1)))
      (G.contMDiff_sqrt_vertical_inner 0) (fun x => G.sqrt_vertical_inner_pos x 0) := by
  apply G.eq_warpedProduct_of_translation_reflection
  · intro x r c v w
    have h := congrArg (fun g : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ) =>
      g.inner (x, r) v w) (htranslate c)
    erw [Diffeomorph.pullbackMetricCross_inner] at h
    change G.inner (x, r + c)
      (mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ))
        (fun z : M × ℝ => (z.1, z.2 + c)) (x, r) v)
      (mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ))
        (fun z : M × ℝ => (z.1, z.2 + c)) (x, r) w) = _ at h
    erw [mfderiv_prod_translation, mfderiv_prod_translation] at h
    exact h
  · intro x r v w
    have h := congrArg (fun g : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ) =>
      g.inner (x, r) v w) hreflect
    erw [Diffeomorph.pullbackMetricCross_inner] at h
    change G.inner (x, -r)
      (mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ))
        (fun z : M × ℝ => (z.1, -z.2)) (x, r) v)
      (mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ))
        (fun z : M × ℝ => (z.1, -z.2)) (x, r) w) = _ at h
    erw [mfderiv_prod_reflection, mfderiv_prod_reflection] at h
    exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SmoothRiemannianMetric.eq_warpedProduct_of_pullback_translation_reflection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SmoothRiemannianMetric.eq_warpedProduct_of_pullback_translation_reflection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SmoothRiemannianMetric.eq_warpedProduct_of_pullback_translation_reflection ``Submission.DifferentialGeometry.SmoothRiemannianMetric.eq_warpedProduct_of_pullback_translation_reflection

end DifferentialGeometry
