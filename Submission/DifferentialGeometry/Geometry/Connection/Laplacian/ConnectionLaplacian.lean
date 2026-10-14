import Submission.DifferentialGeometry.Geometry.Connection.ChartFrame.OrthonormalBasis
import Submission.DifferentialGeometry.Geometry.Operator.Hessian.TraceFormula

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.FiberBundle _root_.NormedSpace _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff


namespace DifferentialGeometry
namespace Geometry
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem

def connLaplacianFunction [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) : M → ℝ :=
  ΔG (I := I) g ⟨_, hf⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.connLaplacianFunction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.connLaplacianFunction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.connLaplacianFunction ``Submission.DifferentialGeometry.Geometry.Connection.connLaplacianFunction

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M] in
@[simp] lemma connLaplacian_function_def [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    connLaplacianFunction (I := I) g hf x = ΔG (I := I) g ⟨_, hf⟩ x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.connLaplacian_function_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.connLaplacian_function_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.connLaplacian_function_def ``Submission.DifferentialGeometry.Geometry.Connection.connLaplacian_function_def

def connLaplacianVector
    (g : SmoothRiemannianMetric I M)
    (V : Π b : M, TangentSpace I b) (x : M) : TangentSpace I x :=
  localConnLapVector (LeviCivita (I := I) g) (smoothOrthoFrame (I := I) g x) V x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.connLaplacianVector then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.connLaplacianVector"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.connLaplacianVector ``Submission.DifferentialGeometry.Geometry.Connection.connLaplacianVector

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] [T2Space M] in
@[simp] lemma connLaplacian_vector_def
    (g : SmoothRiemannianMetric I M)
    (V : Π b : M, TangentSpace I b) (x : M) :
    connLaplacianVector (I := I) g V x =
      localConnLapVector (LeviCivita (I := I) g) (smoothOrthoFrame (I := I) g x)
        V x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.connLaplacian_vector_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.connLaplacian_vector_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.connLaplacian_vector_def ``Submission.DifferentialGeometry.Geometry.Connection.connLaplacian_vector_def

def connLaplacianOneForm
    (g : SmoothRiemannianMetric I M)
    (θ : Π b : M, TangentSpace I b →L[ℝ] ℝ) (x : M) :
    TangentSpace I x →L[ℝ] ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    ((cotangentCov (LeviCivita (I := I) g)).toFun
      (fun b : M => (cotangentCov (LeviCivita (I := I) g)).toFun θ b
        (smoothOrthoFrame (I := I) g x i b)) x
        (smoothOrthoFrame (I := I) g x i x) -
      (cotangentCov (LeviCivita (I := I) g)).toFun θ x
        ((LeviCivita (I := I) g).toFun
          (smoothOrthoFrame (I := I) g x i) x
          (smoothOrthoFrame (I := I) g x i x)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.connLaplacianOneForm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.connLaplacianOneForm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.connLaplacianOneForm ``Submission.DifferentialGeometry.Geometry.Connection.connLaplacianOneForm

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] [T2Space M] in
@[simp] lemma connLaplacian_oneForm_def
    (g : SmoothRiemannianMetric I M)
    (θ : Π b : M, TangentSpace I b →L[ℝ] ℝ) (x : M) :
    connLaplacianOneForm (I := I) g θ x =
      ∑ i : Fin (Module.finrank ℝ E),
        ((cotangentCov (LeviCivita (I := I) g)).toFun
          (fun b : M => (cotangentCov (LeviCivita (I := I) g)).toFun θ b
            (smoothOrthoFrame (I := I) g x i b)) x
            (smoothOrthoFrame (I := I) g x i x) -
          (cotangentCov (LeviCivita (I := I) g)).toFun θ x
            ((LeviCivita (I := I) g).toFun
              (smoothOrthoFrame (I := I) g x i) x
              (smoothOrthoFrame (I := I) g x i x))) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.connLaplacian_oneForm_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.connLaplacian_oneForm_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.connLaplacian_oneForm_def ``Submission.DifferentialGeometry.Geometry.Connection.connLaplacian_oneForm_def

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem connLaplacian_function_eq_laplaceBeltrami [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    connLaplacianFunction (I := I) g hf = ΔG (I := I) g ⟨_, hf⟩ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.connLaplacian_function_eq_laplaceBeltrami then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.connLaplacian_function_eq_laplaceBeltrami"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.connLaplacian_function_eq_laplaceBeltrami ``Submission.DifferentialGeometry.Geometry.Connection.connLaplacian_function_eq_laplaceBeltrami

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem connLaplacian_function_eq_chartHessTrace [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    connLaplacianFunction (I := I) g hf x = chartHessTrace (I := I) g f x := by
  rw [connLaplacian_function_def]
  exact (chartHessTrace_eq_laplacian_pointwise_of_boundaryless
    (I := I) g hf x).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.connLaplacian_function_eq_chartHessTrace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.connLaplacian_function_eq_chartHessTrace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.connLaplacian_function_eq_chartHessTrace ``Submission.DifferentialGeometry.Geometry.Connection.connLaplacian_function_eq_chartHessTrace

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem connLaplacian_function_contMDiff [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (connLaplacianFunction (I := I) g hf) :=
  Δ_g_contMDiff (I := I) g ⟨_, hf⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.connLaplacian_function_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.connLaplacian_function_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.connLaplacian_function_contMDiff ``Submission.DifferentialGeometry.Geometry.Connection.connLaplacian_function_contMDiff

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [BoundarylessManifold I M] in
omit [T2Space M] in
theorem connLaplacian_function_add [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h) (x : M) :
    connLaplacianFunction (I := I) g (hf.add hh) x =
      connLaplacianFunction (I := I) g hf x +
        connLaplacianFunction (I := I) g hh x := by
  rw [connLaplacian_function_def, connLaplacian_function_def,
      connLaplacian_function_def]
  exact Δ_g_add (I := I) g ⟨_, hf⟩ ⟨_, hh⟩ x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.connLaplacian_function_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.connLaplacian_function_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.connLaplacian_function_add ``Submission.DifferentialGeometry.Geometry.Connection.connLaplacian_function_add

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [BoundarylessManifold I M] in
omit [T2Space M] in
theorem connLaplacian_function_const [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (c : ℝ) (x : M) :
    connLaplacianFunction (I := I) g
      (contMDiff_const : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => c)) x = 0 := by
  rw [connLaplacian_function_def]
  exact Δ_g_const (I := I) g c x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.connLaplacian_function_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.connLaplacian_function_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.connLaplacian_function_const ``Submission.DifferentialGeometry.Geometry.Connection.connLaplacian_function_const

omit [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [T2Space M] in
theorem connLaplacian_grad_inner (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} {w : Π b : M, TangentSpace I b} (x : M) :
    g.inner x (connLaplacianVector (I := I) g
                  (fun b => gradFun (I := I) g f b) x) (w x) =
      ∑ i : Fin (Module.finrank ℝ E),
        (g.inner x ((LeviCivita (I := I) g).toFun
                    (covApply (LeviCivita (I := I) g)
                      (smoothOrthoFrame (I := I) g x i)
                      (fun b => gradFun (I := I) g f b)) x
                      (smoothOrthoFrame (I := I) g x i x)) (w x) -
          g.inner x ((LeviCivita (I := I) g).toFun
                      (fun b => gradFun (I := I) g f b) x
                      ((LeviCivita (I := I) g).toFun
                        (smoothOrthoFrame (I := I) g x i) x
                        (smoothOrthoFrame (I := I) g x i x))) (w x)) := by
  rw [connLaplacian_vector_def]
  exact localConnLap_vector_grad_inner_eq_hessian_diff (I := I) g
    (smoothOrthoFrame (I := I) g x) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.connLaplacian_grad_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.connLaplacian_grad_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.connLaplacian_grad_inner ``Submission.DifferentialGeometry.Geometry.Connection.connLaplacian_grad_inner

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem connLaplacian_grad_eq_grad_laplacian_plus_ricciSharp_of_inner
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (hInner : ∀ w : TangentSpace I x,
      g.inner x (connLaplacianVector (I := I) g
                  (fun b => gradFun (I := I) g f b) x) w =
        g.inner x (gradFun (I := I) g (ΔG (I := I) g ⟨_, hf⟩) x) w +
          g.inner x (ricciSharp (I := I) g x (gradFun (I := I) g f x)) w) :
    connLaplacianVector (I := I) g
        (fun b => gradFun (I := I) g f b) x =
      gradFun (I := I) g (ΔG (I := I) g ⟨_, hf⟩) x +
        ricciSharp (I := I) g x (gradFun (I := I) g f x) := by
  unfold connLaplacianVector
  exact heart_of_bochner_smoothOrthoFrame (I := I) g hf x hInner

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.connLaplacian_grad_eq_grad_laplacian_plus_ricciSharp_of_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.connLaplacian_grad_eq_grad_laplacian_plus_ricciSharp_of_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.connLaplacian_grad_eq_grad_laplacian_plus_ricciSharp_of_inner ``Submission.DifferentialGeometry.Geometry.Connection.connLaplacian_grad_eq_grad_laplacian_plus_ricciSharp_of_inner

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem connLaplacian_grad_eq_grad_laplacian_plus_ricciSharp_of_inner_form
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (hInner : ∀ w : TangentSpace I x,
      g.inner x (connLaplacianVector (I := I) g
                  (fun b => gradFun (I := I) g f b) x) w =
        g.inner x (gradFun (I := I) g (ΔG (I := I) g ⟨_, hf⟩) x) w +
          g.inner x (ricciSharp (I := I) g x (gradFun (I := I) g f x)) w) :
    connLaplacianVector (I := I) g
        (fun b => gradFun (I := I) g f b) x =
      gradFun (I := I) g (ΔG (I := I) g ⟨_, hf⟩) x +
        ricciSharp (I := I) g x (gradFun (I := I) g f x) :=
  connLaplacian_grad_eq_grad_laplacian_plus_ricciSharp_of_inner
    (I := I) g hf x hInner

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.connLaplacian_grad_eq_grad_laplacian_plus_ricciSharp_of_inner_form then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.connLaplacian_grad_eq_grad_laplacian_plus_ricciSharp_of_inner_form"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.connLaplacian_grad_eq_grad_laplacian_plus_ricciSharp_of_inner_form ``Submission.DifferentialGeometry.Geometry.Connection.connLaplacian_grad_eq_grad_laplacian_plus_ricciSharp_of_inner_form

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem connLaplacian_grad_iff_inner_form [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    connLaplacianVector (I := I) g
        (fun b => gradFun (I := I) g f b) x =
      gradFun (I := I) g (ΔG (I := I) g ⟨_, hf⟩) x +
        ricciSharp (I := I) g x (gradFun (I := I) g f x) ↔
      ∀ w : TangentSpace I x,
        g.inner x (connLaplacianVector (I := I) g
                    (fun b => gradFun (I := I) g f b) x) w =
          g.inner x (gradFun (I := I) g (ΔG (I := I) g ⟨_, hf⟩) x) w +
            g.inner x (ricciSharp (I := I) g x (gradFun (I := I) g f x)) w := by
  classical
  refine ⟨fun h w => ?_, fun h => ?_⟩
  · rw [h]
    rw [show g.inner x (gradFun (I := I) g (ΔG (I := I) g ⟨_, hf⟩) x +
          ricciSharp (I := I) g x (gradFun (I := I) g f x)) w =
        g.inner x (gradFun (I := I) g (ΔG (I := I) g ⟨_, hf⟩) x) w +
          g.inner x (ricciSharp (I := I) g x (gradFun (I := I) g f x)) w from
      by rw [map_add, add_apply]]
  · exact connLaplacian_grad_eq_grad_laplacian_plus_ricciSharp_of_inner
      (I := I) g hf x h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.connLaplacian_grad_iff_inner_form then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.connLaplacian_grad_iff_inner_form"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.connLaplacian_grad_iff_inner_form ``Submission.DifferentialGeometry.Geometry.Connection.connLaplacian_grad_iff_inner_form

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
theorem connLaplacian_grad_inner_hessian (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} {w : Π b : M, TangentSpace I b} (x : M) :
    g.inner x (connLaplacianVector (I := I) g
                  (fun b => gradFun (I := I) g f b) x) (w x) =
      ∑ i : Fin (Module.finrank ℝ E),
        (g.inner x ((LeviCivita (I := I) g).toFun
                    (covApply (LeviCivita (I := I) g)
                      (smoothOrthoFrame (I := I) g x i)
                      (fun b => gradFun (I := I) g f b)) x
                      (smoothOrthoFrame (I := I) g x i x)) (w x) -
          g.inner x ((LeviCivita (I := I) g).toFun
                      (fun b => gradFun (I := I) g f b) x
                      ((LeviCivita (I := I) g).toFun
                        (smoothOrthoFrame (I := I) g x i) x
                        (smoothOrthoFrame (I := I) g x i x))) (w x)) :=
  connLaplacian_grad_inner (I := I) g x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.connLaplacian_grad_inner_hessian then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.connLaplacian_grad_inner_hessian"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.connLaplacian_grad_inner_hessian ``Submission.DifferentialGeometry.Geometry.Connection.connLaplacian_grad_inner_hessian

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem connLaplacian_grad_hessian_symm [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {X Y : Π b : M, TangentSpace I b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    g.inner x ((LeviCivita (I := I) g).toFun
                  (fun b => gradFun (I := I) g f b) x (X x)) (Y x) =
      g.inner x ((LeviCivita (I := I) g).toFun
                  (fun b => gradFun (I := I) g f b) x (Y x)) (X x) :=
  inner_cov_gradFun_symm (I := I) g hf hX hY

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.connLaplacian_grad_hessian_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.connLaplacian_grad_hessian_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.connLaplacian_grad_hessian_symm ``Submission.DifferentialGeometry.Geometry.Connection.connLaplacian_grad_hessian_symm

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem connLaplacian_grad_curvature_term [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {B w : Π b : M, TangentSpace I b} {x : M}
    (hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% B))
    (hw : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% w)) :
    g.inner x (riemannSec (LeviCivita (I := I) g) B w
                (fun b => gradFun (I := I) g f b) x) (B x) =
      - g.inner x (gradFun (I := I) g f x)
          (riemannSec (LeviCivita (I := I) g) B w B x) :=
  inner_riemannSec_gradFun_skew_symm (I := I) g hf hB hw

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.connLaplacian_grad_curvature_term then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.connLaplacian_grad_curvature_term"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.connLaplacian_grad_curvature_term ``Submission.DifferentialGeometry.Geometry.Connection.connLaplacian_grad_curvature_term

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem smoothOrthoFrame_orthonormal_center
    (g : SmoothRiemannianMetric I M) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    g.inner x
        (smoothOrthoFrame (I := I) g x i x)
        (smoothOrthoFrame (I := I) g x j x) =
      if i = j then 1 else 0 :=
  smoothOrthoFrame_orthonormal_at_center (I := I) g x i j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.smoothOrthoFrame_orthonormal_center then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.smoothOrthoFrame_orthonormal_center"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.smoothOrthoFrame_orthonormal_center ``Submission.DifferentialGeometry.Geometry.Connection.smoothOrthoFrame_orthonormal_center

omit [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem smoothOrthoFrame_isSmooth
    (g : SmoothRiemannianMetric I M) (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (smoothOrthoFrame (I := I) g x i)) :=
  smoothOrthoFrame_smooth (I := I) g x i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.smoothOrthoFrame_isSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.smoothOrthoFrame_isSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.smoothOrthoFrame_isSmooth ``Submission.DifferentialGeometry.Geometry.Connection.smoothOrthoFrame_isSmooth

def frobeniusSqGradVector
    (g : SmoothRiemannianMetric I M)
    (V : Π b : M, TangentSpace I b) (x : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    g.inner x
      ((LeviCivita (I := I) g).toFun V x
        (smoothOrthoFrame (I := I) g x i x))
      ((LeviCivita (I := I) g).toFun V x
        (smoothOrthoFrame (I := I) g x i x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.frobeniusSqGradVector then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.frobeniusSqGradVector"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.frobeniusSqGradVector ``Submission.DifferentialGeometry.Geometry.Connection.frobeniusSqGradVector

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] [T2Space M] in
@[simp] lemma frobeniusSq_grad_vector_def
    (g : SmoothRiemannianMetric I M)
    (V : Π b : M, TangentSpace I b) (x : M) :
    frobeniusSqGradVector (I := I) g V x =
      ∑ i : Fin (Module.finrank ℝ E),
        g.inner x
          ((LeviCivita (I := I) g).toFun V x
            (smoothOrthoFrame (I := I) g x i x))
          ((LeviCivita (I := I) g).toFun V x
            (smoothOrthoFrame (I := I) g x i x)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.frobeniusSq_grad_vector_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.frobeniusSq_grad_vector_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.frobeniusSq_grad_vector_def ``Submission.DifferentialGeometry.Geometry.Connection.frobeniusSq_grad_vector_def

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] [T2Space M] in
lemma frobeniusSq_grad_vector_nonneg
    (g : SmoothRiemannianMetric I M)
    (V : Π b : M, TangentSpace I b) (x : M) :
    0 ≤ frobeniusSqGradVector (I := I) g V x := by
  unfold frobeniusSqGradVector
  refine Finset.sum_nonneg ?_
  intro i _
  set v : TangentSpace I x :=
    (LeviCivita (I := I) g).toFun V x
      (smoothOrthoFrame (I := I) g x i x) with hv_def
  by_cases hv : v = 0
  · simp [hv]
  · exact le_of_lt (g.pos x v hv)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.frobeniusSq_grad_vector_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.frobeniusSq_grad_vector_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.frobeniusSq_grad_vector_nonneg ``Submission.DifferentialGeometry.Geometry.Connection.frobeniusSq_grad_vector_nonneg

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] in
theorem frobeniusSqGradVector_eq_zero_iff
    (g : SmoothRiemannianMetric I M)
    (V : Π b : M, TangentSpace I b) (x : M) :
    frobeniusSqGradVector (I := I) g V x = 0 ↔ (LeviCivita (I := I) g).toFun V x = 0 := by
  classical
  constructor
  · intro hzero
    let L := (LeviCivita (I := I) g).toFun V x
    let b := smoothOrthoFrameBasis g x
    have hsum : ∑ i : Fin (Module.finrank ℝ E), g.inner x (L (b i)) (L (b i)) = 0 := by
      simpa only [b, smoothOrthoFrameBasis_apply, L, frobeniusSqGradVector] using hzero
    have hnonneg (i : Fin (Module.finrank ℝ E)) : 0 ≤ g.inner x (L (b i)) (L (b i)) := by
      by_cases hi : L (b i) = 0
      · simp [hi]
      · exact (g.pos x (L (b i)) hi).le
    have hbzero (i : Fin (Module.finrank ℝ E)) : L (b i) = 0 := by
      have hi : g.inner x (L (b i)) (L (b i)) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnonneg j)).mp hsum i (Finset.mem_univ i)
      by_contra hne
      exact (g.pos x (L (b i)) hne).ne' hi
    change L = 0
    ext v
    rw [← b.sum_repr v, map_sum]
    simp only [map_smul, hbzero, smul_zero, Finset.sum_const_zero, zero_apply]
  · intro hzero
    simp only [frobeniusSqGradVector, hzero, zero_apply,
      map_zero, Finset.sum_const_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.frobeniusSqGradVector_eq_zero_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.frobeniusSqGradVector_eq_zero_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.frobeniusSqGradVector_eq_zero_iff ``Submission.DifferentialGeometry.Geometry.Connection.frobeniusSqGradVector_eq_zero_iff

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
theorem connLaplacian_inner_self_of_trace [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {V : Π b : M, TangentSpace I b}
    (hgVV : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun b : M => g.inner b (V b) (V b)))
    (x : M)
    (hLeibniz :
      ΔG (I := I) g ⟨_, hgVV⟩ x =
        2 * g.inner x (connLaplacianVector (I := I) g V x) (V x) +
          2 * frobeniusSqGradVector (I := I) g V x) :
    connLaplacianFunction (I := I) g hgVV x =
      2 * g.inner x (connLaplacianVector (I := I) g V x) (V x) +
        2 * frobeniusSqGradVector (I := I) g V x := by
  rw [connLaplacian_function_def]
  exact hLeibniz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.connLaplacian_inner_self_of_trace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.connLaplacian_inner_self_of_trace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.connLaplacian_inner_self_of_trace ``Submission.DifferentialGeometry.Geometry.Connection.connLaplacian_inner_self_of_trace

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma mvfderiv_inner_self
    (g : SmoothRiemannianMetric I M)
    {V : Π b : M, TangentSpace I b}
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V)) (x : M)
    (X : TangentSpace I x) :
    mvfderiv (I := I) (fun b => g.inner b (V b) (V b)) x X =
      2 * g.inner x ((LeviCivita (I := I) g).toFun V x X) (V x) := by
  classical
  have hV_at : MDiffAt (T% V) x := (hV x).mdifferentiableAt (by simp)
  have hmc :=
    (LeviCivita_isMetricCompatible (I := I) g).apply hV_at hV_at X
  have hext_eq : mvfderiv (I := I) (fun b => g.inner b (V b) (V b)) x X =
      (mfderiv I 𝓘(ℝ) (fun b : M => g.inner b (V b) (V b)) x) X := rfl
  rw [hext_eq, hmc]
  rw [g.symm x (V x) ((LeviCivita (I := I) g).toFun V x X)]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.mvfderiv_inner_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.mvfderiv_inner_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.mvfderiv_inner_self ``Submission.DifferentialGeometry.Geometry.Connection.mvfderiv_inner_self

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma mvfderiv_inner_self_eq_globally (g : SmoothRiemannianMetric I M)
    {V : Π b : M, TangentSpace I b}
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V))
    (X : Π b : M, TangentSpace I b) :
    (fun b : M => mvfderiv (I := I) (fun b' => g.inner b' (V b') (V b')) b
        (X b)) =
      (fun b : M => 2 * g.inner b
        ((LeviCivita (I := I) g).toFun V b (X b)) (V b)) := by
  funext b
  exact mvfderiv_inner_self (I := I) g hV b (X b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.mvfderiv_inner_self_eq_globally then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.mvfderiv_inner_self_eq_globally"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.mvfderiv_inner_self_eq_globally ``Submission.DifferentialGeometry.Geometry.Connection.mvfderiv_inner_self_eq_globally

end Connection
end Geometry
end DifferentialGeometry
