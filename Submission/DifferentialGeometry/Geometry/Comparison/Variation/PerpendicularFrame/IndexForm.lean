import Submission.DifferentialGeometry.Analysis.ODE.IndexForm.Basic
import Submission.DifferentialGeometry.Geometry.Comparison.Variation.Jacobi.Coordinates
import Submission.DifferentialGeometry.Geometry.Comparison.Variation.Jacobi.Orthogonality
import Submission.DifferentialGeometry.Geometry.Comparison.Variation.PerpendicularFrame.Basic
import Submission.DifferentialGeometry.Geometry.Comparison.Variation.SecondVariation.Basic
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Ricci.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

open _root_.Set _root_.Function _root_.Manifold _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Topology _root_.Manifold _root_.ContDiff _root_.RealInnerProductSpace

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.AlongCurve
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma real_inner_mul (a b : ℝ) : _root_.Inner.inner ℝ a b = b * a := by
  simp [RCLike.inner_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.real_inner_mul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.Variation.real_inner_mul target :: scope.openDecls } }

omit [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [Fintype ι] [DecidableEq ι]
  [T2Space M] [SigmaCompactSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private lemma g_inner_contDiff
    (g : SmoothRiemannianMetric I M)
    {γ : ℝ → M} {v w : ∀ t : ℝ, TangentSpace I (γ t)}
    (hv : ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E)) ∞
      (fun t : ℝ => TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _)) (γ t) (v t)))
    (hw : ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E)) ∞
      (fun t : ℝ => TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _)) (γ t) (w t))) :
    ContDiff ℝ ∞ (fun t : ℝ => g.inner (γ t) (v t) (w t)) := by
  let rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hinner := ContMDiff.inner_bundle (F := E) (B := M)
    (E := (TangentSpace I : M → Type _)) (b := γ) (v := v) (w := w) hv hw
  have hcm : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      (fun t : ℝ => g.inner (γ t) (v t) (w t)) := by
    refine hinner.congr (fun t => ?_)
    rfl
  rw [← contMDiff_iff_contDiff]
  exact hcm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.g_inner_contDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.Variation.g_inner_contDiff target :: scope.openDecls } }

def perpFrameLift {γ : ℝ → M}
    (F : ι → ∀ t : ℝ, TangentSpace I (γ t))
    (y : ℝ → EuclideanSpace ℝ ι) (t : ℝ) :
    TangentSpace I (γ t) :=
  ∑ i, y t i • F i t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.perpFrameLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.perpFrameLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.perpFrameLift ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.perpFrameLift

def perpCoeff (g : SmoothRiemannianMetric I M) {γ : ℝ → M}
    (F : ι → ∀ t : ℝ, TangentSpace I (γ t))
    (Y : ∀ t : ℝ, TangentSpace I (γ t)) (t : ℝ) :
    EuclideanSpace ℝ ι :=
  (EuclideanSpace.equiv ι ℝ).symm
    (fun i => g.inner (γ t) (F i t) (Y t))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.perpCoeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.perpCoeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.perpCoeff ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.perpCoeff

omit [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] [Fintype ι] [DecidableEq ι] in
omit [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] in
@[simp]
theorem perpCoeff_apply
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M}
    (F : ι → ∀ t : ℝ, TangentSpace I (γ t))
    (Y : ∀ t : ℝ, TangentSpace I (γ t)) (t : ℝ) (i : ι) :
    perpCoeff (I := I) g F Y t i = g.inner (γ t) (F i t) (Y t) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.perpCoeff_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.perpCoeff_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.perpCoeff_apply ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.perpCoeff_apply

omit [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [Fintype ι] [DecidableEq ι]
  [T2Space M] [SigmaCompactSpace M] in
@[simp]
theorem perpCoeff_zero
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M}
    (F : ι → ∀ t : ℝ, TangentSpace I (γ t))
    (Y : ∀ t : ℝ, TangentSpace I (γ t)) (t : ℝ) (hY : Y t = 0) :
    perpCoeff (I := I) g F Y t = 0 := by
  apply (EuclideanSpace.equiv ι ℝ).injective
  ext i
  simp only [perpCoeff, ContinuousLinearEquiv.apply_symm_apply, map_zero,
    Pi.zero_apply, hY]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.perpCoeff_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.perpCoeff_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.perpCoeff_zero ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.perpCoeff_zero

omit [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] [DecidableEq ι] in
theorem perpCoeff_smooth
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M}
    (F : ι → ∀ t : ℝ, TangentSpace I (γ t))
    (Y : ∀ t : ℝ, TangentSpace I (γ t))
    (hF : ∀ i, ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t => TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _)) (γ t) (F i t)))
    (hY : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t => TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _)) (γ t) (Y t))) :
    ContDiff ℝ ∞ (perpCoeff (I := I) g F Y) := by
  have hcomponents : ContDiff ℝ ∞
      (fun t : ℝ => fun i => g.inner (γ t) (F i t) (Y t)) :=
    contDiff_pi.2 fun i => g_inner_contDiff (I := I) g (hF i) hY
  exact (ContinuousLinearEquiv.contDiff
    (EuclideanSpace.equiv ι ℝ).symm).comp hcomponents

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.perpCoeff_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.perpCoeff_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.perpCoeff_smooth ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.perpCoeff_smooth

def perpCurvOp (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (F : ι → ∀ t : ℝ, TangentSpace I (γ t)) (t : ℝ) :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  (Matrix.toLpLin 2 2
    (fun i j =>
      g.inner (γ t)
        ((DifferentialGeometry.Geometry.Curvature.riemannOp
            (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
            (γ t))
          (F j t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)))
        (F i t))).toContinuousLinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.perpCurvOp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.perpCurvOp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.perpCurvOp ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.perpCurvOp

omit [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] in
@[simp]
theorem perpCurvOp_apply
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (F : ι → ∀ t : ℝ, TangentSpace I (γ t))
    (t : ℝ) (y : EuclideanSpace ℝ ι) (i : ι) :
    perpCurvOp (I := I) g γ F t y i =
      ∑ j, g.inner (γ t)
        ((DifferentialGeometry.Geometry.Curvature.riemannOp
            (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
            (γ t))
          (F j t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)))
        (F i t) * y j := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.perpCurvOp_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.perpCurvOp_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.perpCurvOp_apply ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.perpCurvOp_apply

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem perpCurv_smooth
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (F : ι → ∀ t : ℝ, TangentSpace I (γ t))
    (hF : ∀ i, ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t => TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _)) (γ t) (F i t))) :
    ContDiff ℝ ∞ (perpCurvOp (I := I) g γ F) := by
  classical
  have hunit : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent ∞
      (fun t : ℝ => TotalSpace.mk' ℝ
        (E := (TangentSpace 𝓘(ℝ, ℝ) : ℝ → Type _)) t (1 : ℝ)) := by
    intro t
    rw [_root_.Bundle.contMDiffAt_totalSpace]
    refine ⟨contMDiffAt_id, ?_⟩
    simpa only [trivializationAt_model_space_apply] using
      (contMDiffAt_const (c := (1 : ℝ)))
  have hvel : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t : ℝ => TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _)) (γ t)
          (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))) := by
    change ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (tangentMap 𝓘(ℝ, ℝ) I γ ∘ fun t : ℝ =>
        TotalSpace.mk' ℝ
          (E := (TangentSpace 𝓘(ℝ, ℝ) : ℝ → Type _)) t (1 : ℝ))
    exact (hγ.contMDiff_tangentMap (le_refl _)).comp hunit
  let : NormedAddCommGroup (E →L[ℝ] E) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E →L[ℝ] E) :=
    ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) :=
    ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) :=
    ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (E × (E →L[ℝ] E)) :=
    Prod.normedAddCommGroup
  let : NormedSpace ℝ (E × (E →L[ℝ] E)) :=
    Prod.normedSpace
  let : NormedAddCommGroup (E × (E →L[ℝ] E →L[ℝ] E)) :=
    Prod.normedAddCommGroup
  let : NormedSpace ℝ (E × (E →L[ℝ] E →L[ℝ] E)) :=
    Prod.normedSpace
  let : NormedAddCommGroup
      (E × (E →L[ℝ] E →L[ℝ] E →L[ℝ] E)) :=
    Prod.normedAddCommGroup
  let : NormedSpace ℝ
      (E × (E →L[ℝ] E →L[ℝ] E →L[ℝ] E)) :=
    Prod.normedSpace
  have hR0 :=
    (DifferentialGeometry.Geometry.Curvature.riemannOp_section_contMDiff
      (I := I) (M := M) g).comp hγ
  have hR1 (j : ι) :=
    ContMDiff.clm_bundle_apply
      (F₁ := E) (F₂ := E →L[ℝ] E →L[ℝ] E)
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun x : M =>
        TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x)
      (b := γ)
      (ϕ := fun t =>
        DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
          (γ t))
      (v := fun t => F j t) hR0 (hF j)
  have hR2 (j : ι) :=
    ContMDiff.clm_bundle_apply
      (F₁ := E) (F₂ := E →L[ℝ] E)
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
      (b := γ)
      (ϕ := fun t =>
        (DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
          (γ t)) (F j t))
      (v := fun t => mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
      (hR1 j) hvel
  have hR3 (j : ι) :=
    ContMDiff.clm_bundle_apply
      (F₁ := E) (F₂ := E)
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun x : M => TangentSpace I x)
      (b := γ)
      (ϕ := fun t =>
        (DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
          (γ t)) (F j t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)))
      (v := fun t => mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
      (hR2 j) hvel
  have hcoeff (i j : ι) : ContDiff ℝ ∞
      (fun t : ℝ => g.inner (γ t)
        ((DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
          (γ t)) (F j t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
            (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)))
        (F i t)) :=
    g_inner_contDiff (I := I) g (hR3 j) (hF i)
  rw [contDiff_clm_apply_iff]
  intro y
  rw [contDiff_euclidean]
  intro i
  simp only [perpCurvOp_apply]
  exact ContDiff.sum fun j _ => (hcoeff i j).mul contDiff_const

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.perpCurv_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.perpCurv_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.perpCurv_smooth ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.perpCurv_smooth

omit [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [DecidableEq ι] in
@[simp]
theorem perpLift_zero {γ : ℝ → M}
    (F : ι → ∀ t : ℝ, TangentSpace I (γ t))
    (y : ℝ → EuclideanSpace ℝ ι) (t : ℝ) (hy : y t = 0) :
    perpFrameLift (I := I) F y t = 0 := by
  simp [perpFrameLift, hy]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.perpLift_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.perpLift_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.perpLift_zero ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.perpLift_zero

omit [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] [DecidableEq ι] in
theorem perpLift_perp
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M}
    (F : ι → ∀ t : ℝ, TangentSpace I (γ t))
    (y : ℝ → EuclideanSpace ℝ ι) (t : ℝ)
    (u : TangentSpace I (γ t))
    (hperp : ∀ i, g.inner (γ t) (F i t) u = 0) :
    g.inner (γ t) (perpFrameLift (I := I) F y t) u = 0 := by
  simp [perpFrameLift, map_sum, map_smul, hperp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.perpLift_perp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.perpLift_perp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.perpLift_perp ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.perpLift_perp

omit [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] in
theorem perpLift_inner
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M}
    (F : ι → ∀ t : ℝ, TangentSpace I (γ t))
    (y z : EuclideanSpace ℝ ι) (t : ℝ)
    (hON : ∀ i j, g.inner (γ t) (F i t) (F j t) =
      if i = j then 1 else 0) :
    g.inner (γ t)
        (∑ i, y i • F i t) (∑ j, z j • F j t) =
      inner ℝ y z := by
  classical
  rw [PiLp.inner_apply]
  simp [map_sum, map_smul, hON, mul_ite]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.perpLift_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.perpLift_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.perpLift_inner ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.perpLift_inner

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem perpFrame_expand
    (g : SmoothRiemannianMetric I M) {x : M}
    (F : ι → TangentSpace I x) (u Z : TangentSpace I x)
    (hcard : Fintype.card ι = Module.finrank ℝ E - 1)
    (hu : 0 < g.inner x u u)
    (hFperp : ∀ i, g.inner x (F i) u = 0)
    (hZperp : g.inner x Z u = 0)
    (hON : ∀ i j, g.inner x (F i) (F j) =
      if i = j then 1 else 0) :
    Z = ∑ i, g.inner x (F i) Z • F i := by
  classical
  let φ : TangentSpace I x →ₗ[ℝ] ℝ := (g.inner x u).toLinearMap
  let W : Submodule ℝ (TangentSpace I x) := LinearMap.ker φ
  have hφu : 0 < φ u := hu
  have hφsurj : Function.Surjective φ := by
    intro c
    refine ⟨(c / φ u) • u, ?_⟩
    calc
      φ ((c / φ u) • u) = (c / φ u) • φ u := φ.map_smul (c / φ u) u
      _ = c := by
        rw [smul_eq_mul]
        exact div_mul_cancel₀ c hφu.ne'
  have hrange : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.mpr hφsurj
  have hfrange : Module.finrank ℝ ↥(LinearMap.range φ) = 1 := by
    rw [hrange]
    simp
  have hfinrankW :
      Module.finrank ℝ ↥W = Module.finrank ℝ (TangentSpace I x) - 1 := by
    have hsum := LinearMap.finrank_range_add_finrank_ker φ
    rw [hfrange] at hsum
    have : Module.finrank ℝ ↥W =
        Module.finrank ℝ ↥(LinearMap.ker φ) := rfl
    rw [this]
    omega
  have hFmem : ∀ i, F i ∈ W := by
    intro i
    change φ (F i) = 0
    change g.inner x u (F i) = 0
    rw [g.symm x u (F i)]
    exact hFperp i
  have hZmem : Z ∈ W := by
    change φ Z = 0
    change g.inner x u Z = 0
    rw [g.symm x u Z]
    exact hZperp
  have hLI : LinearIndependent ℝ F := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have hpair : g.inner x (∑ j, c j • F j) (F i) = 0 := by
      rw [hc]
      simp
    rw [map_sum, sum_apply] at hpair
    rw [Finset.sum_eq_single i] at hpair
    · rw [ContinuousLinearMap.map_smul, smul_apply,
        hON i i, if_pos rfl, smul_eq_mul, mul_one] at hpair
      exact hpair
    · intro j _ hji
      rw [ContinuousLinearMap.map_smul, smul_apply,
        hON j i, if_neg hji, smul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  let vW : ι → W := fun i => ⟨F i, hFmem i⟩
  have hLIW : LinearIndependent ℝ vW := by
    apply LinearIndependent.of_comp W.subtype
    change LinearIndependent ℝ F
    exact hLI
  have hdim : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E := rfl
  have hcardW : Fintype.card ι = Module.finrank ℝ W := by
    rw [hcard, ← hdim, hfinrankW]
  have hspan : Submodule.span ℝ (Set.range vW) = ⊤ :=
    hLIW.span_eq_top_of_card_eq_finrank' hcardW
  let bW : Module.Basis ι ℝ W := Module.Basis.mk hLIW hspan.ge
  have hbW (i : ι) : bW i = vW i := by
    simp only [bW, Module.Basis.coe_mk]
  let zW : W := ⟨Z, hZmem⟩
  let a : ι → ℝ := fun i => bW.repr zW i
  have hsum := bW.sum_repr zW
  have hco := congrArg (fun z : W => (z : TangentSpace I x)) hsum
  have hZsum : Z = ∑ i, a i • F i := by
    symm at hco
    simpa only [a, zW, vW, hbW, Submodule.coe_sum,
      Submodule.coe_smul_of_tower] using hco
  have ha (i : ι) : a i = g.inner x (F i) Z := by
    have hsum_inner :
        g.inner x (F i) (∑ j, a j • F j) = a i := by
      rw [map_sum, Finset.sum_eq_single i]
      · rw [map_smul, hON i i, if_pos rfl, smul_eq_mul, mul_one]
      · intro j _ hji
        rw [map_smul, hON i j, if_neg (Ne.symm hji), smul_zero]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    calc
      a i = g.inner x (F i) (∑ j, a j • F j) := hsum_inner.symm
      _ = g.inner x (F i) Z := by rw [← hZsum]
  calc
    Z = ∑ i, a i • F i := hZsum
    _ = ∑ i, g.inner x (F i) Z • F i :=
      Finset.sum_congr rfl fun i _ => by rw [ha i]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.perpFrame_expand then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.perpFrame_expand"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.perpFrame_expand ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.perpFrame_expand

omit [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem perpLift_coeff
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M}
    (F : ι → ∀ t : ℝ, TangentSpace I (γ t))
    (Y : ∀ t : ℝ, TangentSpace I (γ t)) (t : ℝ)
    (hcard : Fintype.card ι = Module.finrank ℝ E - 1)
    (hvel : 0 < g.inner (γ t) (curveVelocity (I := I) γ t)
      (curveVelocity (I := I) γ t))
    (hFperp : ∀ i, g.inner (γ t) (F i t)
      (curveVelocity (I := I) γ t) = 0)
    (hYperp : g.inner (γ t) (Y t)
      (curveVelocity (I := I) γ t) = 0)
    (hON : ∀ i j, g.inner (γ t) (F i t) (F j t) =
      if i = j then 1 else 0) :
    perpFrameLift (I := I) F (perpCoeff (I := I) g F Y) t = Y t := by
  symm
  simpa only [perpFrameLift, perpCoeff_apply] using
    perpFrame_expand (I := I) g (fun i => F i t)
      (curveVelocity (I := I) γ t) (Y t) hcard hvel hFperp hYperp hON

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.perpLift_coeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.perpLift_coeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.perpLift_coeff ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.perpLift_coeff

omit [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem perpCoeff_ne_zero
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M}
    (F : ι → ∀ t : ℝ, TangentSpace I (γ t))
    (Y : ∀ t : ℝ, TangentSpace I (γ t)) (t : ℝ)
    (hcard : Fintype.card ι = Module.finrank ℝ E - 1)
    (hvel : 0 < g.inner (γ t) (curveVelocity (I := I) γ t)
      (curveVelocity (I := I) γ t))
    (hFperp : ∀ i, g.inner (γ t) (F i t)
      (curveVelocity (I := I) γ t) = 0)
    (hYperp : g.inner (γ t) (Y t)
      (curveVelocity (I := I) γ t) = 0)
    (hON : ∀ i j, g.inner (γ t) (F i t) (F j t) =
      if i = j then 1 else 0)
    (hYne : Y t ≠ 0) :
    perpCoeff (I := I) g F Y t ≠ 0 := by
  intro hcoeff
  apply hYne
  rw [← perpLift_coeff (I := I) g F Y t hcard hvel
    hFperp hYperp hON]
  exact perpLift_zero (I := I) F (perpCoeff (I := I) g F Y) t hcoeff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.perpCoeff_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.perpCoeff_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.perpCoeff_ne_zero ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.perpCoeff_ne_zero

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] in
theorem perpCurv_coeff
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (F : ι → ∀ t : ℝ, TangentSpace I (γ t))
    (Y : ∀ t : ℝ, TangentSpace I (γ t)) (t : ℝ)
    (hcard : Fintype.card ι = Module.finrank ℝ E - 1)
    (hvel : 0 < g.inner (γ t) (curveVelocity (I := I) γ t)
      (curveVelocity (I := I) γ t))
    (hFperp : ∀ i, g.inner (γ t) (F i t)
      (curveVelocity (I := I) γ t) = 0)
    (hYperp : g.inner (γ t) (Y t)
      (curveVelocity (I := I) γ t) = 0)
    (hON : ∀ i j, g.inner (γ t) (F i t) (F j t) =
      if i = j then 1 else 0)
    (i : ι) :
    g.inner (γ t) (F i t)
        ((DifferentialGeometry.Geometry.Curvature.riemannOp
            (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
            (γ t))
          (Y t) (curveVelocity (I := I) γ t)
          (curveVelocity (I := I) γ t)) =
      perpCurvOp (I := I) g γ F t (perpCoeff (I := I) g F Y t) i := by
  classical
  let : NormedAddCommGroup (E →L[ℝ] E) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E →L[ℝ] E) :=
    ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) :=
    ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) :=
    ContinuousLinearMap.toNormedSpace
  have hYexp := perpFrame_expand (I := I) g (fun j => F j t)
    (curveVelocity (I := I) γ t) (Y t) hcard hvel hFperp hYperp hON
  have hcurv := congrArg
    (fun Z : TangentSpace I (γ t) =>
      (DifferentialGeometry.Geometry.Curvature.riemannOp
        (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
        (γ t))
        Z (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t))
    hYexp
  have hpair := congrArg (fun Z : TangentSpace I (γ t) =>
    g.inner (γ t) (F i t) Z) hcurv
  refine hpair.trans ?_
  simp only [map_sum, map_smul, sum_apply,
    smul_apply, smul_eq_mul]
  rw [perpCurvOp_apply]
  simp only [perpCoeff_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [g.symm (γ t) (F i t)
    ((DifferentialGeometry.Geometry.Curvature.riemannOp
      (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
      (γ t))
      (F j t) (curveVelocity (I := I) γ t)
      (curveVelocity (I := I) γ t))]
  simp only [curveVelocity]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.perpCurv_coeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.perpCurv_coeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.perpCurv_coeff ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.perpCurv_coeff

omit [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] in
theorem perpCoeff_ode
    {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (F : ι → ∀ t : ℝ, TangentSpace I (γ t))
    (Y : ∀ t : ℝ, TangentSpace I (γ t)) (t : ℝ)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I n γ t)
    (hFdiff : ∀ i, DifferentiableAt ℝ
      (chartRepAt (I := I) γ (F i) t) t)
    (hYdiff : DifferentiableAt ℝ
      (chartRepAt (I := I) γ Y t) t)
    (hDYdiff : DifferentiableAt ℝ
      (chartRepAt (I := I) γ
        (fun s => covDerivAlong (I := I) g γ Y s) t) t)
    (hFpar : ∀ i, covDerivAlong (I := I) g γ (F i) t = 0)
    (hY : IsJacobiAt (I := I) g γ Y t)
    (hcard : Fintype.card ι = Module.finrank ℝ E - 1)
    (hvel : 0 < g.inner (γ t) (curveVelocity (I := I) γ t)
      (curveVelocity (I := I) γ t))
    (hFperp : ∀ i, g.inner (γ t) (F i t)
      (curveVelocity (I := I) γ t) = 0)
    (hYperp : g.inner (γ t) (Y t)
      (curveVelocity (I := I) γ t) = 0)
    (hON : ∀ i j, g.inner (γ t) (F i t) (F j t) =
      if i = j then 1 else 0) :
    HasDerivAt (perpCoeff (I := I) g F Y)
        (perpCoeff (I := I) g F
          (fun s => covDerivAlong (I := I) g γ Y s) t) t ∧
      HasDerivAt
        (perpCoeff (I := I) g F
          (fun s => covDerivAlong (I := I) g γ Y s))
        (-(perpCurvOp (I := I) g γ F t)
          (perpCoeff (I := I) g F Y t)) t := by
  classical
  let L : (ι → ℝ) ≃L[ℝ] EuclideanSpace ℝ ι :=
    (EuclideanSpace.equiv ι ℝ).symm
  constructor
  · have hpi : HasDerivAt
        (fun s => (fun i => g.inner (γ s) (F i s) (Y s) : ι → ℝ))
        (fun i => g.inner (γ t) (F i t)
          (covDerivAlong (I := I) g γ Y t)) t :=
      hasDerivAt_pi.mpr fun i =>
        parInner_deriv (I := I) hn g γ (F i) Y t hγ
          (hFdiff i) hYdiff (hFpar i)
    have hL := L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hpi
    change HasDerivAt
      ((fun z : ι → ℝ => (EuclideanSpace.equiv ι ℝ).symm z) ∘
        fun s => fun i => g.inner (γ s) (F i s) (Y s))
      ((EuclideanSpace.equiv ι ℝ).symm
        (fun i => g.inner (γ t) (F i t)
          (covDerivAlong (I := I) g γ Y t))) t
    exact hL
  · have hpi : HasDerivAt
        (fun s => (fun i => g.inner (γ s) (F i s)
          (covDerivAlong (I := I) g γ Y s) : ι → ℝ))
        ((EuclideanSpace.equiv ι ℝ)
          (-(perpCurvOp (I := I) g γ F t)
            (perpCoeff (I := I) g F Y t))) t := by
      rw [hasDerivAt_pi]
      intro i
      have hi := parInner_d2 (I := I) hn g γ (F i) Y t hγ
        (hFdiff i) hDYdiff (hFpar i) hY
      rw [perpCurv_coeff (I := I) g γ F Y t hcard hvel
        hFperp hYperp hON i] at hi
      simpa using hi
    have hL := L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hpi
    change HasDerivAt
      ((fun z : ι → ℝ => (EuclideanSpace.equiv ι ℝ).symm z) ∘
        fun s => fun i => g.inner (γ s) (F i s)
          (covDerivAlong (I := I) g γ Y s))
      (-(perpCurvOp (I := I) g γ F t)
        (perpCoeff (I := I) g F Y t)) t
    simpa only [L, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply] using hL

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.perpCoeff_ode then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.perpCoeff_ode"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.perpCoeff_ode ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.perpCoeff_ode

omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [DecidableEq ι] in
omit [NeZero (Module.finrank ℝ E)] in
theorem perpLift_covDeriv
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (F : ι → ∀ t : ℝ, TangentSpace I (γ t))
    (y : ℝ → EuclideanSpace ℝ ι) (t : ℝ)
    (hy : DifferentiableAt ℝ y t)
    (hFdiff : ∀ i, DifferentiableAt ℝ
      (chartRepAt (I := I) γ (F i) t) t)
    (hpar : ∀ i, covDerivAlong (I := I) g γ (F i) t = 0) :
    covDerivAlong (I := I) g γ
        (fun s => perpFrameLift (I := I) F y s) t =
      perpFrameLift (I := I) F (deriv y) t := by
  classical
  have hyi : ∀ i, DifferentiableAt ℝ (fun s => y s i) t := by
    intro i
    exact (EuclideanSpace.proj i).differentiableAt.comp t hy
  have hderiv : ∀ i, deriv (fun s => y s i) t = deriv y t i := by
    intro i
    have hcomp :=
      (EuclideanSpace.proj i).hasFDerivAt.comp_hasDerivAt t hy.hasDerivAt
    change deriv ((fun x : EuclideanSpace ℝ ι => x.ofLp i) ∘ y) t =
      (deriv y t).ofLp i
    exact hcomp.deriv
  change covDerivAlong (I := I) g γ
      (fun s => ∑ i, y s i • F i s) t =
    ∑ i, deriv y t i • F i t
  rw [covDerivAlong_expand (I := I) g γ Finset.univ
    (fun i s => y s i) F t (fun i _ => hyi i)
    (fun i _ => hFdiff i) (fun i _ => hpar i)]
  exact Finset.sum_congr rfl fun i _ => by rw [hderiv i]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.perpLift_covDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.perpLift_covDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.perpLift_covDeriv ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.perpLift_covDeriv

omit [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] [DecidableEq ι] in
theorem perpLift_smooth
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (F : ι → ∀ t : ℝ, TangentSpace I (γ t))
    (y : ℝ → EuclideanSpace ℝ ι) (hy : ContDiff ℝ ∞ y)
    (hF : ∀ i, ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t => TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _)) (γ t) (F i t))) :
    ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t => TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _)) (γ t)
          (perpFrameLift (I := I) F y t)) := by
  classical
  intro t₀
  rw [_root_.Bundle.contMDiffAt_totalSpace]
  refine ⟨hγ t₀, ?_⟩
  have hyi : ∀ i, ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      (fun t => y t i) t₀ := by
    intro i
    rw [contMDiffAt_iff_contDiffAt]
    exact ((EuclideanSpace.proj i).contDiff.comp hy).contDiffAt
  have hFfib : ∀ i, ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞
      (fun t =>
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) (γ t₀))
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (γ t) (F i t))).2) t₀ := by
    intro i
    exact ((_root_.Bundle.contMDiffAt_totalSpace (f := fun t : ℝ =>
      TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
        (γ t) (F i t))).1 (hF i t₀)).2
  have hsum : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞
      (fun t => ∑ i,
        y t i •
          ((_root_.FiberBundle.trivializationAt E (TangentSpace I) (γ t₀))
            (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
              (γ t) (F i t))).2) t₀ :=
    ContMDiffAt.sum fun i _ => (hyi i).smul (hFfib i)
  refine hsum.congr_of_eventuallyEq ?_
  have hbase : ∀ᶠ t in 𝓝 t₀,
      γ t ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) (γ t₀)).baseSet := by
    have hmem : γ t₀ ∈
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) (γ t₀)).baseSet :=
      FiberBundle.mem_baseSet_trivializationAt' (γ t₀)
    exact (hγ t₀).continuousAt.preimage_mem_nhds
      ((_root_.FiberBundle.trivializationAt E (TangentSpace I) (γ t₀)).open_baseSet.mem_nhds hmem)
  filter_upwards [hbase] with t ht
  simp only [perpFrameLift, TotalSpace.mk']
  rw [(_root_.FiberBundle.trivializationAt E (TangentSpace I) (γ t₀)).apply_eq_prod_continuousLinearEquivAt
    ℝ (γ t) ht]
  simp only [map_sum, map_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(_root_.FiberBundle.trivializationAt E (TangentSpace I) (γ t₀)).apply_eq_prod_continuousLinearEquivAt
    ℝ (γ t) ht]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.perpLift_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.perpLift_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.perpLift_smooth ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.perpLift_smooth

omit [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] in
theorem perpCurv_inner
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (F : ι → ∀ t : ℝ, TangentSpace I (γ t))
    (y z : EuclideanSpace ℝ ι) (t : ℝ) :
    inner ℝ (perpCurvOp (I := I) g γ F t y) z =
      g.inner (γ t)
        ((DifferentialGeometry.Geometry.Curvature.riemannOp
            (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
            (γ t))
          (∑ j, y j • F j t)
          (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)))
        (∑ i, z i • F i t) := by
  classical
  rw [PiLp.inner_apply]
  simp only [perpCurvOp_apply]
  simp only [map_sum, map_smul, sum_apply,
    smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_mul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.perpCurv_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.perpCurv_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.perpCurv_inner ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.perpCurv_inner

omit [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] in
theorem perpCurv_symm
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (F : ι → ∀ t : ℝ, TangentSpace I (γ t))
    (t : ℝ) (y z : EuclideanSpace ℝ ι) :
    inner ℝ (perpCurvOp (I := I) g γ F t y) z =
      inner ℝ y (perpCurvOp (I := I) g γ F t z) := by
  rw [perpCurv_inner (I := I) g γ F y z t]
  rw [DifferentialGeometry.Geometry.Curvature.riemannOp_diag_symm
    (I := I) g (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
    (∑ j, y j • F j t) (∑ i, z i • F i t)]
  rw [g.symm (γ t)
    (∑ j, y j • F j t)
    ((DifferentialGeometry.Geometry.Curvature.riemannOp
        (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
        (γ t))
      (∑ i, z i • F i t)
      (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)))]
  rw [← perpCurv_inner (I := I) g γ F z y t]
  exact real_inner_comm _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.perpCurv_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.perpCurv_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.perpCurv_symm ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.perpCurv_symm

omit [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] in
theorem perpLift_integrand
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (F : ι → ∀ t : ℝ, TangentSpace I (γ t))
    (y z : ℝ → EuclideanSpace ℝ ι) (t : ℝ)
    (hy : DifferentiableAt ℝ y t) (hz : DifferentiableAt ℝ z t)
    (hFdiff : ∀ i, DifferentiableAt ℝ
      (chartRepAt (I := I) γ (F i) t) t)
    (hpar : ∀ i, covDerivAlong (I := I) g γ (F i) t = 0)
    (hON : ∀ i j, g.inner (γ t) (F i t) (F j t) =
      if i = j then 1 else 0) :
    indexFormIntegrand (I := I) g γ
        (fun s => perpFrameLift (I := I) F y s)
        (fun s => perpFrameLift (I := I) F z s) t =
      DifferentialGeometry.Analysis.ODE.indexIntegrand
        (perpCurvOp (I := I) g γ F) y (deriv y) z (deriv z) t := by
  simp only [indexFormIntegrand,
    DifferentialGeometry.Analysis.ODE.indexIntegrand]
  rw [perpLift_covDeriv (I := I) g γ F y t hy hFdiff hpar,
    perpLift_covDeriv (I := I) g γ F z t hz hFdiff hpar]
  simp only [perpFrameLift]
  rw [perpLift_inner (I := I) g F (deriv y t) (deriv z t) t hON]
  rw [perpCurv_inner (I := I) g γ F (y t) (z t) t]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.perpLift_integrand then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.perpLift_integrand"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.perpLift_integrand ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.perpLift_integrand

omit [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] in
theorem perpLift_indexForm
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (F : ι → ∀ t : ℝ, TangentSpace I (γ t))
    (y z : ℝ → EuclideanSpace ℝ ι) (a b : ℝ)
    (hy : ∀ t ∈ _root_.Set.uIcc a b, DifferentiableAt ℝ y t)
    (hz : ∀ t ∈ _root_.Set.uIcc a b, DifferentiableAt ℝ z t)
    (hFdiff : ∀ i, ∀ t ∈ _root_.Set.uIcc a b, DifferentiableAt ℝ
      (chartRepAt (I := I) γ (F i) t) t)
    (hpar : ∀ i, ∀ t ∈ _root_.Set.uIcc a b,
      covDerivAlong (I := I) g γ (F i) t = 0)
    (hON : ∀ t ∈ _root_.Set.uIcc a b, ∀ i j,
      g.inner (γ t) (F i t) (F j t) = if i = j then 1 else 0) :
    indexForm (I := I) g γ a b
        (fun t => perpFrameLift (I := I) F y t)
        (fun t => perpFrameLift (I := I) F z t) =
      DifferentialGeometry.Analysis.ODE.indexForm
        (perpCurvOp (I := I) g γ F) a b y (deriv y) z (deriv z) := by
  rw [indexForm_eq_intervalIntegral,
    DifferentialGeometry.Analysis.ODE.indexForm_def]
  refine intervalIntegral.integral_congr fun t ht => ?_
  exact perpLift_integrand (I := I) g γ F y z t
    (hy t ht) (hz t ht) (fun i => hFdiff i t ht)
    (fun i => hpar i t ht) (hON t ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.perpLift_indexForm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.perpLift_indexForm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.perpLift_indexForm ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.perpLift_indexForm

end Variation
end Riemannian
end Geometry
end DifferentialGeometry

end
