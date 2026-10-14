import Submission.DifferentialGeometry.Analysis.Elliptic.Operator.SmoothBridge
import Submission.DifferentialGeometry.Analysis.Elliptic.Operator.SmoothDenseLp

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

theorem resolvent_injective (g : SmoothRiemannianMetric I M) :
    Function.Injective (resolvent (I := I) (M := M) g) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  have h_orth : ∀ v : H1Compl g,
      ⟪H1ComplToLp (I := I) (M := M) g v, f⟫_ℝ = 0 := by
    intro v
    have h := resolvent_inner_eq_lpFunctional (I := I) (M := M) g f v
    rw [hf] at h
    rw [inner_zero_left] at h
    linarith
  have h_dense : DenseRange (H1ComplToLp (I := I) (M := M) g) :=
    denseRange_H1ComplToLp (I := I) (M := M) g
  have h_inner_zero : ∀ w : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g),
      (innerSL ℝ f) w = 0 := by
    intro w
    have h_eq_on_range :
        (fun y : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) =>
            (innerSL ℝ f) y) ∘ (H1ComplToLp (I := I) (M := M) g) =
        (fun _ : H1Compl g => (0 : ℝ)) := by
      funext v
      change ⟪f, H1ComplToLp (I := I) (M := M) g v⟫_ℝ = 0
      rw [real_inner_comm]
      exact h_orth v
    have h_func_eq :
        (fun y : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) =>
            (innerSL ℝ f) y) =
        (fun _ : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) => (0 : ℝ)) :=
      h_dense.equalizer (innerSL ℝ f).continuous continuous_const h_eq_on_range
    have := congrFun h_func_eq w
    exact this
  have h_self : ⟪f, f⟫_ℝ = 0 := by
    have := h_inner_zero f
    rwa [innerSL_apply_apply] at this
  rw [real_inner_self_eq_norm_sq] at h_self
  have h_norm_zero : ‖f‖ = 0 := by
    have h_pow_zero : ‖f‖ ^ 2 = 0 := h_self
    exact pow_eq_zero_iff (two_ne_zero) |>.mp h_pow_zero
  exact norm_eq_zero.mp h_norm_zero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.resolvent_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.resolvent_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.resolvent_injective ``Submission.DifferentialGeometry.Analysis.Laplacian.resolvent_injective

def laplacianDomain (g : SmoothRiemannianMetric I M) :
    Submodule ℝ (H1Compl g) :=
  LinearMap.range (resolvent (I := I) (M := M) g).toLinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.laplacianDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.laplacianDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.laplacianDomain ``Submission.DifferentialGeometry.Analysis.Laplacian.laplacianDomain

lemma laplacianDomain_mem_iff (g : SmoothRiemannianMetric I M) {u : H1Compl g} :
    u ∈ laplacianDomain (I := I) (M := M) g ↔
      ∃ f : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g),
        u = resolvent (I := I) (M := M) g f := by
  unfold laplacianDomain
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨f, hf⟩; exact ⟨f, hf.symm⟩
  · rintro ⟨f, hf⟩; exact ⟨f, hf.symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.laplacianDomain_mem_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.laplacianDomain_mem_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.laplacianDomain_mem_iff ``Submission.DifferentialGeometry.Analysis.Laplacian.laplacianDomain_mem_iff

def laplacianDomain.preimage (g : SmoothRiemannianMetric I M)
    (u : laplacianDomain (I := I) (M := M) g) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  Classical.choose ((laplacianDomain_mem_iff (I := I) (M := M) g).mp u.2)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Analysis.Laplacian.laplacianDomain
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.laplacianDomain.preimage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.laplacianDomain.preimage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.laplacianDomain.preimage ``Submission.DifferentialGeometry.Analysis.Laplacian.laplacianDomain.preimage

@[simp] lemma resolvent_laplacianDomain_preimage_eq
    (g : SmoothRiemannianMetric I M)
    (u : laplacianDomain (I := I) (M := M) g) :
    resolvent (I := I) (M := M) g
        (laplacianDomain.preimage (I := I) (M := M) g u) =
      (u : H1Compl g) :=
  (Classical.choose_spec ((laplacianDomain_mem_iff (I := I) (M := M) g).mp u.2)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.resolvent_laplacianDomain_preimage_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.resolvent_laplacianDomain_preimage_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.resolvent_laplacianDomain_preimage_eq ``Submission.DifferentialGeometry.Analysis.Laplacian.resolvent_laplacianDomain_preimage_eq

lemma laplacianDomain_preimage_zero (g : SmoothRiemannianMetric I M) :
    laplacianDomain.preimage (I := I) (M := M) g
        (0 : laplacianDomain (I := I) (M := M) g) = 0 := by
  apply resolvent_injective (I := I) (M := M) g
  rw [resolvent_laplacianDomain_preimage_eq]
  rw [(resolvent (I := I) (M := M) g).map_zero]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.laplacianDomain_preimage_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.laplacianDomain_preimage_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.laplacianDomain_preimage_zero ``Submission.DifferentialGeometry.Analysis.Laplacian.laplacianDomain_preimage_zero

lemma laplacianDomain_preimage_add (g : SmoothRiemannianMetric I M)
    (u v : laplacianDomain (I := I) (M := M) g) :
    laplacianDomain.preimage (I := I) (M := M) g (u + v) =
      laplacianDomain.preimage (I := I) (M := M) g u +
      laplacianDomain.preimage (I := I) (M := M) g v := by
  apply resolvent_injective (I := I) (M := M) g
  rw [resolvent_laplacianDomain_preimage_eq]
  rw [(resolvent (I := I) (M := M) g).map_add]
  rw [resolvent_laplacianDomain_preimage_eq, resolvent_laplacianDomain_preimage_eq]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.laplacianDomain_preimage_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.laplacianDomain_preimage_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.laplacianDomain_preimage_add ``Submission.DifferentialGeometry.Analysis.Laplacian.laplacianDomain_preimage_add

lemma laplacianDomain_preimage_smul (g : SmoothRiemannianMetric I M)
    (c : ℝ) (u : laplacianDomain (I := I) (M := M) g) :
    laplacianDomain.preimage (I := I) (M := M) g (c • u) =
      c • laplacianDomain.preimage (I := I) (M := M) g u := by
  apply resolvent_injective (I := I) (M := M) g
  rw [resolvent_laplacianDomain_preimage_eq]
  rw [(resolvent (I := I) (M := M) g).map_smul]
  rw [resolvent_laplacianDomain_preimage_eq]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.laplacianDomain_preimage_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.laplacianDomain_preimage_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.laplacianDomain_preimage_smul ``Submission.DifferentialGeometry.Analysis.Laplacian.laplacianDomain_preimage_smul

def laplacianDomain.preimageLin (g : SmoothRiemannianMetric I M) :
    laplacianDomain (I := I) (M := M) g →ₗ[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) where
  toFun := laplacianDomain.preimage (I := I) (M := M) g
  map_add' := laplacianDomain_preimage_add (I := I) (M := M) g
  map_smul' c u := laplacianDomain_preimage_smul (I := I) (M := M) g c u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.laplacianDomain.preimageLin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.laplacianDomain.preimageLin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.laplacianDomain.preimageLin ``Submission.DifferentialGeometry.Analysis.Laplacian.laplacianDomain.preimageLin

def laplacianOp (g : SmoothRiemannianMetric I M) :
    laplacianDomain (I := I) (M := M) g →ₗ[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  ((H1ComplToLp (I := I) (M := M) g).toLinearMap.comp
    (laplacianDomain (I := I) (M := M) g).subtype) -
  laplacianDomain.preimageLin (I := I) (M := M) g

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.laplacianOp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.laplacianOp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.laplacianOp ``Submission.DifferentialGeometry.Analysis.Laplacian.laplacianOp

@[simp] lemma laplacianOp_apply (g : SmoothRiemannianMetric I M)
    (u : laplacianDomain (I := I) (M := M) g) :
    laplacianOp (I := I) (M := M) g u =
      H1ComplToLp (I := I) (M := M) g (u : H1Compl g) -
        laplacianDomain.preimage (I := I) (M := M) g u := by
  unfold laplacianOp
  rw [LinearMap.sub_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.laplacianOp_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.laplacianOp_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.laplacianOp_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.laplacianOp_apply

theorem laplacianOp_resolvent (g : SmoothRiemannianMetric I M)
    (f : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    laplacianOp (I := I) (M := M) g
        ⟨resolvent (I := I) (M := M) g f,
          (laplacianDomain_mem_iff (I := I) (M := M) g).mpr ⟨f, rfl⟩⟩ =
      H1ComplToLp (I := I) (M := M) g (resolvent (I := I) (M := M) g f) - f := by
  rw [laplacianOp_apply]
  have h_preimage_eq :
      laplacianDomain.preimage (I := I) (M := M) g
          ⟨resolvent (I := I) (M := M) g f,
            (laplacianDomain_mem_iff (I := I) (M := M) g).mpr ⟨f, rfl⟩⟩ = f := by
    apply resolvent_injective (I := I) (M := M) g
    rw [resolvent_laplacianDomain_preimage_eq]
  rw [h_preimage_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.laplacianOp_resolvent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.laplacianOp_resolvent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.laplacianOp_resolvent ``Submission.DifferentialGeometry.Analysis.Laplacian.laplacianOp_resolvent

lemma smoothToH1Compl_mem_laplacianDomain
    {g : SmoothRiemannianMetric I M} (u : SmoothScalar g) :
    smoothToH1Compl (I := I) (M := M) g u ∈
      laplacianDomain (I := I) (M := M) g := by
  rw [laplacianDomain_mem_iff]
  refine ⟨smoothToLp (I := I) (M := M) g u.oneSubLapClassical, ?_⟩
  exact smoothToH1Compl_eq_resolvent_oneSubLap (I := I) (M := M) u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.smoothToH1Compl_mem_laplacianDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.smoothToH1Compl_mem_laplacianDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.smoothToH1Compl_mem_laplacianDomain ``Submission.DifferentialGeometry.Analysis.Laplacian.smoothToH1Compl_mem_laplacianDomain

theorem laplacianOp_smoothToH1Compl
    {g : SmoothRiemannianMetric I M} (u : SmoothScalar g) :
    laplacianOp (I := I) (M := M) g
        ⟨smoothToH1Compl (I := I) (M := M) g u,
          smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) u⟩ =
      smoothToLp (I := I) (M := M) g u -
        smoothToLp (I := I) (M := M) g u.oneSubLapClassical := by
  rw [show (⟨smoothToH1Compl (I := I) (M := M) g u,
        smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) u⟩ :
        laplacianDomain (I := I) (M := M) g) =
      ⟨resolvent (I := I) (M := M) g
        (smoothToLp (I := I) (M := M) g u.oneSubLapClassical),
        (laplacianDomain_mem_iff (I := I) (M := M) g).mpr
          ⟨smoothToLp (I := I) (M := M) g u.oneSubLapClassical, rfl⟩⟩ from ?_]
  · rw [laplacianOp_resolvent]
    have h_eq : resolvent (I := I) (M := M) g
          (smoothToLp (I := I) (M := M) g u.oneSubLapClassical) =
        smoothToH1Compl (I := I) (M := M) g u :=
      (smoothToH1Compl_eq_resolvent_oneSubLap (I := I) (M := M) u).symm
    rw [h_eq, H1ComplToLp_smoothToH1Compl]
  · apply Subtype.ext
    exact smoothToH1Compl_eq_resolvent_oneSubLap (I := I) (M := M) u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.laplacianOp_smoothToH1Compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.laplacianOp_smoothToH1Compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.laplacianOp_smoothToH1Compl ``Submission.DifferentialGeometry.Analysis.Laplacian.laplacianOp_smoothToH1Compl

theorem laplacianOp_smoothToH1Compl_eq_smoothToLp_laplacian
    {g : SmoothRiemannianMetric I M} (u : SmoothScalar g) :
    laplacianOp (I := I) (M := M) g
        ⟨smoothToH1Compl (I := I) (M := M) g u,
          smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) u⟩ =
      smoothToLp (I := I) (M := M) g u.laplacian := by
  rw [laplacianOp_smoothToH1Compl]
  rw [← map_sub, SmoothScalar.sub_oneSubLapClassical]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.laplacianOp_smoothToH1Compl_eq_smoothToLp_laplacian then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.laplacianOp_smoothToH1Compl_eq_smoothToLp_laplacian"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.laplacianOp_smoothToH1Compl_eq_smoothToLp_laplacian ``Submission.DifferentialGeometry.Analysis.Laplacian.laplacianOp_smoothToH1Compl_eq_smoothToLp_laplacian

private lemma h1Inner_eq_lpInner_with_preimage
    (g : SmoothRiemannianMetric I M)
    (u v : laplacianDomain (I := I) (M := M) g) :
    ⟪(u : H1Compl g), (v : H1Compl g)⟫_ℝ =
      ⟪H1ComplToLp (I := I) (M := M) g (v : H1Compl g),
        laplacianDomain.preimage (I := I) (M := M) g u⟫_ℝ := by
  have h_u_eq : (u : H1Compl g) = resolvent (I := I) (M := M) g
      (laplacianDomain.preimage (I := I) (M := M) g u) :=
    (resolvent_laplacianDomain_preimage_eq (I := I) (M := M) g u).symm
  rw [h_u_eq]
  exact resolvent_inner_eq_lpFunctional (I := I) (M := M) g
    (laplacianDomain.preimage (I := I) (M := M) g u) (v : H1Compl g)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.h1Inner_eq_lpInner_with_preimage
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.h1Inner_eq_lpInner_with_preimage target :: scope.openDecls } }

private lemma lpInner_preimage_swap
    (g : SmoothRiemannianMetric I M)
    (u v : laplacianDomain (I := I) (M := M) g) :
    ⟪H1ComplToLp (I := I) (M := M) g (v : H1Compl g),
        laplacianDomain.preimage (I := I) (M := M) g u⟫_ℝ =
      ⟪H1ComplToLp (I := I) (M := M) g (u : H1Compl g),
        laplacianDomain.preimage (I := I) (M := M) g v⟫_ℝ := by
  rw [← h1Inner_eq_lpInner_with_preimage (I := I) (M := M) g u v]
  rw [← h1Inner_eq_lpInner_with_preimage (I := I) (M := M) g v u]
  exact real_inner_comm _ _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.lpInner_preimage_swap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.lpInner_preimage_swap target :: scope.openDecls } }

theorem laplacianOp_symmetric (g : SmoothRiemannianMetric I M)
    (u v : laplacianDomain (I := I) (M := M) g) :
    ⟪H1ComplToLp (I := I) (M := M) g (u : H1Compl g),
        laplacianOp (I := I) (M := M) g v⟫_ℝ =
      ⟪laplacianOp (I := I) (M := M) g u,
        H1ComplToLp (I := I) (M := M) g (v : H1Compl g)⟫_ℝ := by
  rw [laplacianOp_apply, laplacianOp_apply]
  rw [inner_sub_right, inner_sub_left]
  have h_swap := lpInner_preimage_swap (I := I) (M := M) g v u
  have h_swap_inner :
      ⟪H1ComplToLp (I := I) (M := M) g (u : H1Compl g),
          laplacianDomain.preimage (I := I) (M := M) g v⟫_ℝ =
        ⟪laplacianDomain.preimage (I := I) (M := M) g u,
          H1ComplToLp (I := I) (M := M) g (v : H1Compl g)⟫_ℝ := by
    rw [h_swap, real_inner_comm]
  linarith [h_swap_inner]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.laplacianOp_symmetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.laplacianOp_symmetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.laplacianOp_symmetric ``Submission.DifferentialGeometry.Analysis.Laplacian.laplacianOp_symmetric

theorem h1Inner_symmetric_on_laplacianDomain
    (g : SmoothRiemannianMetric I M)
    (u v : laplacianDomain (I := I) (M := M) g) :
    ⟪(u : H1Compl g), (v : H1Compl g)⟫_ℝ =
      ⟪(v : H1Compl g), (u : H1Compl g)⟫_ℝ :=
  real_inner_comm _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.h1Inner_symmetric_on_laplacianDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.h1Inner_symmetric_on_laplacianDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.h1Inner_symmetric_on_laplacianDomain ``Submission.DifferentialGeometry.Analysis.Laplacian.h1Inner_symmetric_on_laplacianDomain

end Laplacian
end Analysis
end DifferentialGeometry

end
