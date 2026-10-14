import Submission.DifferentialGeometry.Geometry.Metric.Pullback.Basic
import Submission.DifferentialGeometry.Geometry.Metric.Comparison.BallMonotonicity
import Submission.DifferentialGeometry.Geometry.Metric.Basic
import Submission.DifferentialGeometry.Bundle.ContinuousLinearMapSection.Basic
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Analysis.InnerProductSpace.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry

open _root_.Bundle
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

private lemma infty_ne_zero_cross : (∞ : WithTop ℕ∞) ≠ 0 := by decide

run_cmd do
  let target := ``Submission.DifferentialGeometry.infty_ne_zero_cross
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.infty_ne_zero_cross target :: scope.openDecls } }

noncomputable def Diffeomorph.pullbackInnerCross
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  let step1 : TangentSpace I x →L[ℝ] TangentSpace J (Φ x) →L[ℝ] ℝ :=
    (g.inner (Φ x)).comp (mfderiv I J Φ x)
  let precompOp : (TangentSpace J (Φ x) →L[ℝ] ℝ) →L[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
    ContinuousLinearMap.precomp ℝ (mfderiv I J Φ x)
  precompOp.comp step1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Diffeomorph.pullbackInnerCross then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Diffeomorph.pullbackInnerCross"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Diffeomorph.pullbackInnerCross ``Submission.DifferentialGeometry.Diffeomorph.pullbackInnerCross

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I ∞ M] in
theorem Diffeomorph.pullbackInnerCross_symm
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N)
    (x : M) (v w : TangentSpace I x) :
    Diffeomorph.pullbackInnerCross g Φ x v w
      = Diffeomorph.pullbackInnerCross g Φ x w v := by
  unfold Diffeomorph.pullbackInnerCross
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply]
  exact g.symm (Φ x) _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Diffeomorph.pullbackInnerCross_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Diffeomorph.pullbackInnerCross_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Diffeomorph.pullbackInnerCross_symm ``Submission.DifferentialGeometry.Diffeomorph.pullbackInnerCross_symm

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I ∞ M] in
theorem Diffeomorph.pullbackInnerCross_pos
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N)
    (x : M) (v : TangentSpace I x) (hv : v ≠ 0) :
    0 < Diffeomorph.pullbackInnerCross g Φ x v v := by
  unfold Diffeomorph.pullbackInnerCross
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply]
  set hΦeq : TangentSpace I x ≃L[ℝ] TangentSpace J (Φ x) :=
    Diffeomorph.mfderivToContinuousLinearEquiv Φ infty_ne_zero_cross x with hΦeq_def
  have hvImage : mfderiv I J Φ x v ≠ 0 := by
    have h1 : hΦeq v ≠ 0 := (hΦeq.map_ne_zero_iff).mpr hv
    have h2 : (hΦeq : TangentSpace I x →L[ℝ] TangentSpace J (Φ x)) v
        = mfderiv I J Φ x v := by
      rw [hΦeq_def]
      have heq := Diffeomorph.mfderivToContinuousLinearEquiv_coe (Φ := Φ) (x := x)
        infty_ne_zero_cross
      exact congrArg (fun f : TangentSpace I x →L[ℝ] TangentSpace J (Φ x) => f v) heq
    have hcoe : (hΦeq : TangentSpace I x → TangentSpace J (Φ x)) v = hΦeq v := rfl
    rw [← h2]; exact fun h => h1 (by simpa [hcoe] using h)
  exact g.pos (Φ x) _ hvImage

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Diffeomorph.pullbackInnerCross_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Diffeomorph.pullbackInnerCross_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Diffeomorph.pullbackInnerCross_pos ``Submission.DifferentialGeometry.Diffeomorph.pullbackInnerCross_pos

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I ∞ M] in
theorem inner_comp_smooth_along_diffeoCross
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N) :
    ContMDiff I (J.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
      ((fun b ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) b (g.inner b)) ∘ (Φ : M → N)) :=
  g.contMDiff.comp Φ.contMDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.inner_comp_smooth_along_diffeoCross then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.inner_comp_smooth_along_diffeoCross"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.inner_comp_smooth_along_diffeoCross ``Submission.DifferentialGeometry.inner_comp_smooth_along_diffeoCross

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I ∞ M] in
private theorem pullbackInnerCross_eval
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N)
    (x : M) (v w : TangentSpace I x) :
    Diffeomorph.pullbackInnerCross g Φ x v w
      = g.inner (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x w) := by
  unfold Diffeomorph.pullbackInnerCross
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.pullbackInnerCross_eval
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.pullbackInnerCross_eval target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I ∞ M] [IsManifold J ∞ N] in
private theorem mfderiv_eq_mfderivCLE_applyCross
    (Φ : M ≃ₘ⟮I, J⟯ N) (x : M) (v : TangentSpace I x) :
    Diffeomorph.mfderivToContinuousLinearEquiv Φ infty_ne_zero_cross x v
      = mfderiv I J Φ x v := by
  have h := Diffeomorph.mfderivToContinuousLinearEquiv_coe (Φ := Φ) (x := x) infty_ne_zero_cross
  exact congrArg (fun f : TangentSpace I x →L[ℝ] TangentSpace J (Φ x) => f v) h

run_cmd do
  let target := ``Submission.DifferentialGeometry.mfderiv_eq_mfderivCLE_applyCross
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.mfderiv_eq_mfderivCLE_applyCross target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I ∞ M] in
theorem Diffeomorph.pullbackInnerCross_isVonNBounded
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N) :
    ∀ x : M, Bornology.IsVonNBounded ℝ
      {v : TangentSpace I x | Diffeomorph.pullbackInnerCross g Φ x v v < 1} := by
  intro x
  set hΦeq := Diffeomorph.mfderivToContinuousLinearEquiv Φ infty_ne_zero_cross x with hΦeq_def
  have hg := g.isVonNBounded (Φ x)
  have himg := hg.image (hΦeq.symm : TangentSpace J (Φ x) →L[ℝ] TangentSpace I x)
  have hseteq :
      {v : TangentSpace I x | Diffeomorph.pullbackInnerCross g Φ x v v < 1}
        = ((hΦeq.symm : TangentSpace J (Φ x) →L[ℝ] TangentSpace I x) : _ → _)
            '' {w : TangentSpace J (Φ x) | g.inner (Φ x) w w < 1} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    refine ⟨fun hv => ⟨hΦeq v, ?_, ?_⟩, ?_⟩
    · have h1 := pullbackInnerCross_eval (g := g) (Φ := Φ) x v v
      rw [h1] at hv
      have h2 := mfderiv_eq_mfderivCLE_applyCross (Φ := Φ) (x := x) v
      rw [← h2] at hv
      exact hv
    · change (hΦeq.symm : TangentSpace J (Φ x) → TangentSpace I x) (hΦeq v) = v
      exact hΦeq.symm_apply_apply v
    · rintro ⟨w, hw, rfl⟩
      have hsym : ((hΦeq.symm : TangentSpace J (Φ x) →L[ℝ] TangentSpace I x) :
            TangentSpace J (Φ x) → TangentSpace I x) w = hΦeq.symm w := rfl
      rw [hsym]
      rw [pullbackInnerCross_eval]
      have hImage : mfderiv I J Φ x (hΦeq.symm w) = w := by
        have hmap := mfderiv_eq_mfderivCLE_applyCross (Φ := Φ) (x := x) (hΦeq.symm w)
        rw [← hmap]
        exact hΦeq.apply_symm_apply w
      rw [hImage]; exact hw
  rw [hseteq]
  exact himg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Diffeomorph.pullbackInnerCross_isVonNBounded then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Diffeomorph.pullbackInnerCross_isVonNBounded"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Diffeomorph.pullbackInnerCross_isVonNBounded ``Submission.DifferentialGeometry.Diffeomorph.pullbackInnerCross_isVonNBounded

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
private theorem mfderiv_apply_section_smooth_along_diffeoCross
    (Φ : M ≃ₘ⟮I, J⟯ N)
    (Y : ∀ x : M, TangentSpace I x)
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := TangentSpace I) x (Y x))) :
    ContMDiff I (J.prod 𝓘(ℝ, F)) ∞
      (fun x : M => TotalSpace.mk' F (E := (TangentSpace J : N → Type _))
        (Φ x) (mfderiv I J (Φ : M → N) x (Y x))) := by
  have h_tangentMap : ContMDiff I.tangent J.tangent ∞ (tangentMap I J (Φ : M → N)) :=
    Φ.contMDiff.contMDiff_tangentMap (le_refl _)
  have h := h_tangentMap.comp hY
  exact h

run_cmd do
  let target := ``Submission.DifferentialGeometry.mfderiv_apply_section_smooth_along_diffeoCross
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.mfderiv_apply_section_smooth_along_diffeoCross target :: scope.openDecls } }

noncomputable def Diffeomorph.pullbackMetricCross
    [T2Space M]
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N) :
    SmoothRiemannianMetric I M where
  inner x := Diffeomorph.pullbackInnerCross g Φ x
  symm x v w := Diffeomorph.pullbackInnerCross_symm g Φ x v w
  pos x v hv := Diffeomorph.pullbackInnerCross_pos g Φ x v hv
  isVonNBounded x := Diffeomorph.pullbackInnerCross_isVonNBounded g Φ x
  contMDiff := by
    classical
    apply contMDiff_continuousLinearMap_section_of_apply
      (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
      (φ := fun x : M => Diffeomorph.pullbackInnerCross g Φ x)
    intro Y
    apply contMDiff_continuousLinearMap_section_of_apply
      (V₂ := fun _ : M => ℝ)
      (φ := fun x : M => Diffeomorph.pullbackInnerCross g Φ x (Y x))
    intro W
    have hv := mfderiv_apply_section_smooth_along_diffeoCross Φ (fun x => Y x) Y.contMDiff
    have hw := mfderiv_apply_section_smooth_along_diffeoCross Φ (fun x => W x) W.contMDiff
    have hg : ContMDiff I (J.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
        (fun x : M => TotalSpace.mk'
          (F →L[ℝ] F →L[ℝ] ℝ)
          (E := fun b : N => TangentSpace J b →L[ℝ] TangentSpace J b →L[ℝ] ℝ)
          (Φ x) (g.inner (Φ x))) :=
      g.contMDiff.comp Φ.contMDiff
    have h_total : ContMDiff I (J.prod 𝓘(ℝ, ℝ)) ∞
        (fun x : M => TotalSpace.mk' ℝ
          (E := Bundle.Trivial N ℝ)
          (Φ x)
          (g.inner (Φ x) (mfderiv I J (Φ : M → N) x (Y x))
            (mfderiv I J (Φ : M → N) x (W x)))) :=
      ContMDiff.clm_bundle_apply₂
        (E₁ := fun b : N => TangentSpace J b)
        (E₂ := fun b : N => TangentSpace J b)
        (E₃ := fun _ : N => ℝ)
        (b := fun x : M => Φ x)
        (ψ := fun x : M => g.inner (Φ x))
        (v := fun x : M => mfderiv I J (Φ : M → N) x (Y x))
        (w := fun x : M => mfderiv I J (Φ : M → N) x (W x))
        hg hv hw
    have h_scalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun x : M => g.inner (Φ x) (mfderiv I J (Φ : M → N) x (Y x))
            (mfderiv I J (Φ : M → N) x (W x))) := by
      intro x
      have h_at := h_total x
      rw [_root_.Bundle.contMDiffAt_totalSpace] at h_at
      simpa using h_at.2
    have h_pullback_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Diffeomorph.pullbackInnerCross g Φ x (Y x) (W x)) := by
      have h_eq : (fun x : M => Diffeomorph.pullbackInnerCross g Φ x (Y x) (W x))
          = fun x : M => g.inner (Φ x) (mfderiv I J (Φ : M → N) x (Y x))
              (mfderiv I J (Φ : M → N) x (W x)) := by
        funext x; exact pullbackInnerCross_eval g Φ x (Y x) (W x)
      rw [h_eq]; exact h_scalar
    intro x
    rw [_root_.Bundle.contMDiffAt_section]
    refine (h_pullback_smooth.contMDiffAt).congr_of_eventuallyEq ?_
    filter_upwards with y
    change Diffeomorph.pullbackInnerCross g Φ y (Y y) (W y) =
      (_root_.FiberBundle.trivializationAt ℝ (Bundle.Trivial M ℝ) x
        ⟨y, Diffeomorph.pullbackInnerCross g Φ y (Y y) (W y)⟩).2
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Diffeomorph.pullbackMetricCross then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Diffeomorph.pullbackMetricCross"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Diffeomorph.pullbackMetricCross ``Submission.DifferentialGeometry.Diffeomorph.pullbackMetricCross


omit [FiniteDimensional ℝ F] in
theorem diffeomorph_pullback_metric_existsCross
    [T2Space M]
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N) :
    ∃ g' : SmoothRiemannianMetric I M, g' = Diffeomorph.pullbackMetricCross g Φ :=
  ⟨Diffeomorph.pullbackMetricCross g Φ, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.diffeomorph_pullback_metric_existsCross then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.diffeomorph_pullback_metric_existsCross"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.diffeomorph_pullback_metric_existsCross ``Submission.DifferentialGeometry.diffeomorph_pullback_metric_existsCross

omit [FiniteDimensional ℝ F] in
theorem Diffeomorph.pullbackMetricCross_inner
    [T2Space M]
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N) (x : M) (v w : TangentSpace I x) :
    (Diffeomorph.pullbackMetricCross g Φ).inner x v w
      = g.inner (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x w) :=
  pullbackInnerCross_eval g Φ x v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Diffeomorph.pullbackMetricCross_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Diffeomorph.pullbackMetricCross_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Diffeomorph.pullbackMetricCross_inner ``Submission.DifferentialGeometry.Diffeomorph.pullbackMetricCross_inner

theorem Diffeomorph.pullbackMetricCross_eq_pullbackMetric
    {P : Type*} [TopologicalSpace P] [ChartedSpace H P]
    [IsManifold I ∞ P] [T2Space M]
    (g : SmoothRiemannianMetric I P) (Φ : M ≃ₘ⟮I, I⟯ P) :
    Diffeomorph.pullbackMetricCross g Φ =
      Diffeomorph.pullbackMetric g Φ := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [Diffeomorph.pullbackMetricCross_inner,
    Diffeomorph.pullbackMetric_inner]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Diffeomorph.pullbackMetricCross_eq_pullbackMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Diffeomorph.pullbackMetricCross_eq_pullbackMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Diffeomorph.pullbackMetricCross_eq_pullbackMetric ``Submission.DifferentialGeometry.Diffeomorph.pullbackMetricCross_eq_pullbackMetric

theorem Diffeomorph.pullbackMetricCross_trans
    {W : Type*} [NormedAddCommGroup W] [NormedSpace Real W]
    {L : Type*} [TopologicalSpace L] {K : ModelWithCorners Real W L}
    {P : Type*} [TopologicalSpace P] [ChartedSpace L P] [IsManifold K ∞ P]
    [T2Space M] [T2Space N]
    (g : SmoothRiemannianMetric K P)
    (Φ : M ≃ₘ⟮I, J⟯ N) (Ψ : N ≃ₘ⟮J, K⟯ P) :
    Diffeomorph.pullbackMetricCross
        (Diffeomorph.pullbackMetricCross g Ψ) Φ =
      Diffeomorph.pullbackMetricCross g (Φ.trans Ψ) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [Diffeomorph.pullbackMetricCross_inner,
    Diffeomorph.pullbackMetricCross_inner,
    Diffeomorph.pullbackMetricCross_inner]
  have hcomp : mfderiv I K (Φ.trans Ψ : M → P) x =
      (mfderiv J K (Ψ : N → P) (Φ x)).comp
        (mfderiv I J (Φ : M → N) x) :=
    mfderiv_comp x
      (Ψ.contMDiff.mdifferentiableAt (by simp))
      (Φ.contMDiff.mdifferentiableAt (by simp))
  rw [hcomp]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Diffeomorph.pullbackMetricCross_trans then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Diffeomorph.pullbackMetricCross_trans"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Diffeomorph.pullbackMetricCross_trans ``Submission.DifferentialGeometry.Diffeomorph.pullbackMetricCross_trans

theorem Diffeomorph.pullbackMetricCross_refl
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    Diffeomorph.pullbackMetricCross g (_root_.Diffeomorph.refl I M ∞) = g := by
  rcases g with ⟨inner_g, symm_g, pos_g, isVonN_g, contMDiff_g⟩
  have hinner :
      (fun x => Diffeomorph.pullbackInnerCross
          ⟨inner_g, symm_g, pos_g, isVonN_g, contMDiff_g⟩
          (_root_.Diffeomorph.refl I M ∞) x) = inner_g := by
    funext x
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    rw [pullbackInnerCross_eval]
    have hmfd : mfderiv I I
        (_root_.Diffeomorph.refl I M ∞ : M ≃ₘ⟮I, I⟯ M) x =
        ContinuousLinearMap.id Real (TangentSpace I x) := by
      have h : mfderiv I I
          (fun y : M => (_root_.Diffeomorph.refl I M ∞ : M ≃ₘ⟮I, I⟯ M) y) x =
          mfderiv I I (id : M → M) x := rfl
      rw [h]
      exact mfderiv_id
    have hv : mfderiv I I
        (_root_.Diffeomorph.refl I M ∞ : M ≃ₘ⟮I, I⟯ M) x v = v := by
      rw [hmfd]
      rfl
    have hw : mfderiv I I
        (_root_.Diffeomorph.refl I M ∞ : M ≃ₘ⟮I, I⟯ M) x w = w := by
      rw [hmfd]
      rfl
    rw [hv, hw]
    rfl
  unfold Diffeomorph.pullbackMetricCross
  congr 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Diffeomorph.pullbackMetricCross_refl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Diffeomorph.pullbackMetricCross_refl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Diffeomorph.pullbackMetricCross_refl ``Submission.DifferentialGeometry.Diffeomorph.pullbackMetricCross_refl

theorem Diffeomorph.pullbackMetricCross_symm_eq_iff
    [T2Space M] [T2Space N]
    {g : SmoothRiemannianMetric J N} {h : SmoothRiemannianMetric I M}
    {Φ : M ≃ₘ⟮I, J⟯ N} :
    Diffeomorph.pullbackMetricCross g Φ = h ↔
      Diffeomorph.pullbackMetricCross h Φ.symm = g := by
  constructor
  · intro hEq
    calc
      Diffeomorph.pullbackMetricCross h Φ.symm =
          Diffeomorph.pullbackMetricCross
            (Diffeomorph.pullbackMetricCross g Φ) Φ.symm := by rw [hEq]
      _ = Diffeomorph.pullbackMetricCross g (Φ.symm.trans Φ) :=
        Diffeomorph.pullbackMetricCross_trans g Φ.symm Φ
      _ = g := by
        rw [Φ.symm_trans_self, Diffeomorph.pullbackMetricCross_refl]
  · intro hEq
    calc
      Diffeomorph.pullbackMetricCross g Φ =
          Diffeomorph.pullbackMetricCross
            (Diffeomorph.pullbackMetricCross h Φ.symm) Φ := by rw [hEq]
      _ = Diffeomorph.pullbackMetricCross h (Φ.trans Φ.symm) :=
        Diffeomorph.pullbackMetricCross_trans h Φ Φ.symm
      _ = h := by
        rw [Φ.self_trans_symm, Diffeomorph.pullbackMetricCross_refl]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Diffeomorph.pullbackMetricCross_symm_eq_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Diffeomorph.pullbackMetricCross_symm_eq_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Diffeomorph.pullbackMetricCross_symm_eq_iff ``Submission.DifferentialGeometry.Diffeomorph.pullbackMetricCross_symm_eq_iff

omit [FiniteDimensional ℝ F] in
theorem Diffeomorph.pullbackInnerCross_contMDiff
    [T2Space M]
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x
        ((Diffeomorph.pullbackInnerCross g Φ x : E →L[ℝ] E →L[ℝ] ℝ))) :=
  (Diffeomorph.pullbackMetricCross g Φ).contMDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Diffeomorph.pullbackInnerCross_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Diffeomorph.pullbackInnerCross_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Diffeomorph.pullbackInnerCross_contMDiff ``Submission.DifferentialGeometry.Diffeomorph.pullbackInnerCross_contMDiff

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I ∞ M] [IsManifold J ∞ N] in
theorem Diffeomorph.mfderiv_contMDiffCross
    (Φ : M ≃ₘ⟮I, J⟯ N) :
    ContMDiff I J ∞ (Φ : M → N) :=
  Φ.contMDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Diffeomorph.mfderiv_contMDiffCross then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Diffeomorph.mfderiv_contMDiffCross"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Diffeomorph.mfderiv_contMDiffCross ``Submission.DifferentialGeometry.Diffeomorph.mfderiv_contMDiffCross

end DifferentialGeometry
