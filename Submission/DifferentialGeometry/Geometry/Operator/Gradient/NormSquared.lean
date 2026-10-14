import Submission.DifferentialGeometry.Geometry.Operator.Hessian.Basic
import Submission.DifferentialGeometry.Geometry.Curvature.Riemann.Defs
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tangent.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix

namespace DifferentialGeometry
namespace Geometry
namespace Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure

def normGradSqFun (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) : ℝ :=
  g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g f x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.normGradSqFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.normGradSqFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.normGradSqFun ``Submission.DifferentialGeometry.Geometry.Operator.normGradSqFun

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma normGradSqFun_def
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    normGradSqFun (I := I) g f x =
      g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g f x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.normGradSqFun_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.normGradSqFun_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.normGradSqFun_def ``Submission.DifferentialGeometry.Geometry.Operator.normGradSqFun_def

omit [NeZero (Module.finrank ℝ E)] in
lemma normGradSqFun_nonneg
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    0 ≤ normGradSqFun (I := I) g f x := by
  classical
  by_cases hgf : gradFun (I := I) g f x = 0
  · change 0 ≤ g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g f x)
    rw [hgf]
    have hmap : g.inner x (0 : TangentSpace I x) = (0 : TangentSpace I x →L[ℝ] ℝ) :=
      map_zero _
    rw [hmap]
    exact le_refl _
  · change 0 ≤ g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g f x)
    exact le_of_lt (g.pos x _ hgf)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.normGradSqFun_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.normGradSqFun_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.normGradSqFun_nonneg ``Submission.DifferentialGeometry.Geometry.Operator.normGradSqFun_nonneg

omit [NeZero (Module.finrank ℝ E)] in
theorem normGradSqFun_eq_zero_iff
    {g : SmoothRiemannianMetric I M} {f : M → ℝ} {x : M} :
    normGradSqFun (I := I) g f x = 0 ↔
      mfderiv I 𝓘(ℝ, ℝ) f x = 0 := by
  constructor
  · intro hzero
    have hgrad : gradFun (I := I) g f x = 0 := by
      by_contra hne
      exact (ne_of_gt (g.pos x _ hne)) hzero
    ext v
    rw [← inner_gradFun (I := I) g f x v, hgrad]
    rw [show g.inner x (0 : TangentSpace I x) = 0 from map_zero _]
    rfl
  · intro hzero
    rw [normGradSqFun_def, gradFun_eq_zero_of_mfderiv_eq_zero g f hzero]
    simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.normGradSqFun_eq_zero_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.normGradSqFun_eq_zero_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.normGradSqFun_eq_zero_iff ``Submission.DifferentialGeometry.Geometry.Operator.normGradSqFun_eq_zero_iff

namespace BochnerInternal

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma contMDiff_g_inner
    (g : SmoothRiemannianMetric I M)
    {v w : ∀ x : M, TangentSpace I x}
    (hv : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _)) x (v x)))
    (hw : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _)) x (w x))) :
    ContMDiff I 𝓘(ℝ) ∞ (fun b : M => g.inner b (v b) (w b)) := by
  let rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have h := ContMDiff.inner_bundle (F := E) (B := M) (E := (TangentSpace I : M → Type _))
    (b := fun x => x) (v := v) (w := w) hv hw
  refine h.congr ?_
  intro b
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.BochnerInternal.contMDiff_g_inner
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.BochnerInternal.contMDiff_g_inner target :: scope.openDecls } }

end BochnerInternal

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem contMDiff_g_inner_of_smooth_sections
    (g : SmoothRiemannianMetric I M)
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I 𝓘(ℝ) ∞ (fun b : M => g.inner b (X b) (Y b)) := by
  have hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _)) x (X x)) := X.contMDiff
  have hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _)) x (Y x)) := Y.contMDiff
  exact BochnerInternal.contMDiff_g_inner (I := I) (M := M) g hX hY

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.contMDiff_g_inner_of_smooth_sections then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.contMDiff_g_inner_of_smooth_sections"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.contMDiff_g_inner_of_smooth_sections ``Submission.DifferentialGeometry.Geometry.Operator.contMDiff_g_inner_of_smooth_sections

omit [NeZero (Module.finrank ℝ E)] in
theorem normGradSqFun_continuous [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    Continuous (normGradSqFun (I := I) g f) := by
  let fs : C^∞⟮I, M; ℝ⟯ := ⟨f, hf⟩
  have h :=
    TangentBundle.continuous_g_inner_of_smooth_sections (I := I) (M := M) g
      (gradG (I := I) g fs) (gradG (I := I) g fs)
  refine h.congr ?_
  intro b
  change g.inner b (gradFun (I := I) g f b) (gradFun (I := I) g f b) =
    normGradSqFun (I := I) g f b
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.normGradSqFun_continuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.normGradSqFun_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.normGradSqFun_continuous ``Submission.DifferentialGeometry.Geometry.Operator.normGradSqFun_continuous

omit [NeZero (Module.finrank ℝ E)] in
theorem normGradSqFun_contMDiff [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff I 𝓘(ℝ) ∞ (normGradSqFun (I := I) g f) := by
  let fs : C^∞⟮I, M; ℝ⟯ := ⟨f, hf⟩
  have h :=
    contMDiff_g_inner_of_smooth_sections (I := I) (M := M) g
      (gradG (I := I) g fs) (gradG (I := I) g fs)
  refine h.congr ?_
  intro b
  change g.inner b (gradFun (I := I) g f b) (gradFun (I := I) g f b) =
    normGradSqFun (I := I) g f b
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.normGradSqFun_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.normGradSqFun_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.normGradSqFun_contMDiff ``Submission.DifferentialGeometry.Geometry.Operator.normGradSqFun_contMDiff

end Operator
end Geometry
end DifferentialGeometry
