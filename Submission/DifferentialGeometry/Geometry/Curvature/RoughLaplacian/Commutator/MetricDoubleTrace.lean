import Submission.DifferentialGeometry.Geometry.Curvature.RoughLaplacian.Commutator.TensorSlotSwap
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.HomTensor.SectionCalculus

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Connection.Realization
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

open _root_.Submission.DifferentialGeometry.Geometry.Connection


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Geometry
namespace Curvature

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.TensorMultilinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance _root_.Submission.DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

noncomputable def metricDoubleTraceFib (g : SmoothRiemannianMetric I M) (r t : ℕ) (x : M) :
    TensorRSSpace r (t + 2) I x →L[ℝ] TensorRSSpace r t I x :=
  haveI : FiniteDimensional ℝ (TensorRSSpace r (t + 2) I x) :=
    tensorRSSpaceFiniteDimensional (I := I) (M := M)
  haveI : T2Space (TensorRSSpace r (t + 2) I x) := tensorRSSpaceT2 (I := I) (M := M)
  haveI : T2Space (TensorRSSpace r t I x) := tensorRSSpaceT2 (I := I) (M := M)
  LinearMap.toContinuousLinearMap
    { toFun := fun V =>
        ∑ i : Fin (Module.finrank ℝ E),
          curryLastTwoTensorSlots (I := I) (M := M) r t x V
            (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x i x)
      map_add' := fun V V' => by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [twoSlotPeel_add, add_apply, add_apply]
      map_smul' := fun c V => by
        rw [RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [twoSlotPeel_smul, smul_apply, smul_apply] }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metricDoubleTraceFib then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metricDoubleTraceFib"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metricDoubleTraceFib ``Submission.DifferentialGeometry.Geometry.Curvature.metricDoubleTraceFib

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
lemma metricDoubleTraceFib_apply (g : SmoothRiemannianMetric I M) (r t : ℕ) (x : M)
    (V : TensorRSSpace r (t + 2) I x) :
    metricDoubleTraceFib (I := I) (M := M) g r t x V =
      ∑ i : Fin (Module.finrank ℝ E),
        curryLastTwoTensorSlots (I := I) (M := M) r t x V
          (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x i x) := by
  have : FiniteDimensional ℝ (TensorRSSpace r (t + 2) I x) :=
    tensorRSSpaceFiniteDimensional (I := I) (M := M)
  have : T2Space (TensorRSSpace r (t + 2) I x) := tensorRSSpaceT2 (I := I) (M := M)
  have : T2Space (TensorRSSpace r t I x) := tensorRSSpaceT2 (I := I) (M := M)
  rw [metricDoubleTraceFib, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metricDoubleTraceFib_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metricDoubleTraceFib_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metricDoubleTraceFib_apply ``Submission.DifferentialGeometry.Geometry.Curvature.metricDoubleTraceFib_apply

private noncomputable def metricDoubleTraceFibFixedFrame (r t : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M) :
    TensorRSSpace r (t + 2) I x →L[ℝ] TensorRSSpace r t I x :=
  haveI : FiniteDimensional ℝ (TensorRSSpace r (t + 2) I x) :=
    tensorRSSpaceFiniteDimensional (I := I) (M := M)
  haveI : T2Space (TensorRSSpace r (t + 2) I x) := tensorRSSpaceT2 (I := I) (M := M)
  haveI : T2Space (TensorRSSpace r t I x) := tensorRSSpaceT2 (I := I) (M := M)
  LinearMap.toContinuousLinearMap
    { toFun := fun V =>
        ∑ i : Fin (Module.finrank ℝ E),
          curryLastTwoTensorSlots (I := I) (M := M) r t x V (B i x) (B i x)
      map_add' := fun V V' => by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [twoSlotPeel_add, add_apply, add_apply]
      map_smul' := fun c V => by
        rw [RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [twoSlotPeel_smul, smul_apply, smul_apply] }

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.metricDoubleTraceFibFixedFrame
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.metricDoubleTraceFibFixedFrame target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
private lemma metricDoubleTraceFibFixedFrame_apply (r t : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (V : TensorRSSpace r (t + 2) I x) :
    metricDoubleTraceFibFixedFrame (I := I) (M := M) r t B x V =
      ∑ i : Fin (Module.finrank ℝ E),
        curryLastTwoTensorSlots (I := I) (M := M) r t x V (B i x) (B i x) := by
  have : FiniteDimensional ℝ (TensorRSSpace r (t + 2) I x) :=
    tensorRSSpaceFiniteDimensional (I := I) (M := M)
  have : T2Space (TensorRSSpace r (t + 2) I x) := tensorRSSpaceT2 (I := I) (M := M)
  have : T2Space (TensorRSSpace r t I x) := tensorRSSpaceT2 (I := I) (M := M)
  rw [metricDoubleTraceFibFixedFrame, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.metricDoubleTraceFibFixedFrame_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.metricDoubleTraceFibFixedFrame_apply target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
private lemma metricDoubleTraceFib_eq_fixedFrame_moving (g : SmoothRiemannianMetric I M) (r t : ℕ)
    (x : M) :
    metricDoubleTraceFib (I := I) (M := M) g r t x =
      metricDoubleTraceFibFixedFrame (I := I) (M := M) r t (smoothOrthoFrame (I := I) g x) x := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.metricDoubleTraceFib_eq_fixedFrame_moving
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.metricDoubleTraceFib_eq_fixedFrame_moving target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    in
private theorem metricDoubleTraceFibFixedFrame_contMDiff (r t : ℕ)
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (t + 2) ℝ E →L[ℝ] TensorRSModel r t ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r (t + 2) ℝ E →L[ℝ] TensorRSModel r t ℝ E)
        (E := fun z : M => TensorRSSpace r (t + 2) I z →L[ℝ] TensorRSSpace r t I z) x
        (metricDoubleTraceFibFixedFrame (I := I) (M := M) r t B x)) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (V₁ := fun z : M => TensorRSSpace r (t + 2) I z)
    (V₂ := fun z : M => TensorRSSpace r t I z)
    (φ := fun x => metricDoubleTraceFibFixedFrame (I := I) (M := M) r t B x)
  intro Z
  have hsum : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r t ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r t ℝ E)
        (E := fun z : M => TensorRSSpace r t I z) x
        (∑ i : Fin (Module.finrank ℝ E),
          curryLastTwoTensorSlots (I := I) (M := M) r t x (Z x) (B i x) (B i x))) := by
    refine ContMDiff.sum_section (s := Finset.univ) (fun i _ => ?_)
    have hA :=
      (covGradBundleEquiv_symm_contMDiff_totalSpace (I := I) (M := M) r (t + 1)).comp Z.contMDiff
    have h1 :=
      ContMDiff.clm_bundle_apply (b := id) hA (hB i)
    have h2 :=
      (covGradBundleEquiv_symm_contMDiff_totalSpace (I := I) (M := M) r t).comp h1
    have h3 :=
      ContMDiff.clm_bundle_apply (b := id) h2 (hB i)
    refine h3.congr ?_
    intro x
    rfl
  refine hsum.congr ?_
  intro x
  exact congrArg (TotalSpace.mk' (TensorRSModel r t ℝ E)
    (E := fun z : M => TensorRSSpace r t I z) x)
    (metricDoubleTraceFibFixedFrame_apply (I := I) (M := M) r t B x (Z x)).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.metricDoubleTraceFibFixedFrame_contMDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.metricDoubleTraceFibFixedFrame_contMDiff target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
private theorem metricDoubleTraceFibFixedFrame_frame_independent (g : SmoothRiemannianMetric I M)
    (r t : ℕ)
    {B C : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b} (y : M)
    (hB_orth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner y (B i y) (B j y) = if i = j then (1 : ℝ) else 0)
    (hC_orth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner y (C i y) (C j y) = if i = j then (1 : ℝ) else 0) :
    metricDoubleTraceFibFixedFrame (I := I) (M := M) r t B y =
      metricDoubleTraceFibFixedFrame (I := I) (M := M) r t C y := by
  classical
  refine ContinuousLinearMap.ext (fun V => ?_)
  apply tensorRS_eq_of_eval_eq (I := I) (M := M)
  intro D m
  have hexpand : ∀ F : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b,
      Tensor0SSpace.eval
          ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace t I y from
            metricDoubleTraceFibFixedFrame (I := I) (M := M) r t F y V) D) m =
        ∑ i : Fin (Module.finrank ℝ E),
          Tensor0SSpace.eval
            ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace t I y from
              curryLastTwoTensorSlots (I := I) (M := M) r t y V (F i y) (F i y)) D) m := by
    intro F
    rw [show (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace t I y from
          metricDoubleTraceFibFixedFrame (I := I) (M := M) r t F y V) =
        ∑ i : Fin (Module.finrank ℝ E),
          (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace t I y from
            curryLastTwoTensorSlots (I := I) (M := M) r t y V (F i y) (F i y)) from
      metricDoubleTraceFibFixedFrame_apply (I := I) (M := M) r t F y V]
    rw [sum_apply, Tensor0SSpace.eval_sum]
  rw [hexpand B, hexpand C]
  have : T2Space (TangentSpace I y) := tangentSpaceT2 (I := I) (M := M)
  have : FiniteDimensional ℝ (TangentSpace I y) :=
    tangentSpaceFiniteDimensional (I := I) (M := M)
  set Hb : TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun u =>
          LinearMap.toContinuousLinearMap
            { toFun := fun w => Tensor0SSpace.eval
                ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace t I y from
                  curryLastTwoTensorSlots (I := I) (M := M) r t y V u w) D) m
              map_add' := fun w w' => by
                rw [map_add (curryLastTwoTensorSlots (I := I) (M := M) r t y V u),
                  add_apply,
                  Tensor0SSpace.eval_add]
              map_smul' := fun c w => by
                rw [map_smul (curryLastTwoTensorSlots (I := I) (M := M) r t y V u),
                  smul_apply, Tensor0SSpace.eval_smul]; rfl }
        map_add' := fun u u' => by
          refine ContinuousLinearMap.ext (fun w => ?_)
          change Tensor0SSpace.eval
              ((curryLastTwoTensorSlots (I := I) (M := M) r t y V (u + u') w) D) m =
            Tensor0SSpace.eval ((curryLastTwoTensorSlots (I := I) (M := M) r t y V u w) D) m +
              Tensor0SSpace.eval ((curryLastTwoTensorSlots (I := I) (M := M) r t y V u' w) D) m
          rw [map_add (curryLastTwoTensorSlots (I := I) (M := M) r t y V),
            add_apply,
            add_apply, Tensor0SSpace.eval_add]
        map_smul' := fun c u => by
          refine ContinuousLinearMap.ext (fun w => ?_)
          change Tensor0SSpace.eval
              ((curryLastTwoTensorSlots (I := I) (M := M) r t y V (c • u) w) D) m =
            c • Tensor0SSpace.eval ((curryLastTwoTensorSlots (I := I) (M := M) r t y V u w) D) m
          rw [map_smul (curryLastTwoTensorSlots (I := I) (M := M) r t y V),
            smul_apply,
            smul_apply, Tensor0SSpace.eval_smul] }
    with hHb_def
  have hHb_apply : ∀ u w : TangentSpace I y,
      Hb u w = Tensor0SSpace.eval
        ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace t I y from
          curryLastTwoTensorSlots (I := I) (M := M) r t y V u w) D) m := by
    intro u w
    rw [hHb_def, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.eval
          ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace t I y from
            curryLastTwoTensorSlots (I := I) (M := M) r t y V (B i y) (B i y)) D) m) =
      ∑ i : Fin (Module.finrank ℝ E), Hb (B i y) (B i y) from
    Finset.sum_congr rfl (fun i _ => (hHb_apply (B i y) (B i y)).symm)]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.eval
          ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace t I y from
            curryLastTwoTensorSlots (I := I) (M := M) r t y V (C i y) (C i y)) D) m) =
      ∑ i : Fin (Module.finrank ℝ E), Hb (C i y) (C i y) from
    Finset.sum_congr rfl (fun i _ => (hHb_apply (C i y) (C i y)).symm)]
  rw [orthonormal_basis_bilin_trace (I := I) (M := M) g (x := y) Hb (fun i => B i y) hB_orth,
    orthonormal_basis_bilin_trace (I := I) (M := M) g (x := y) Hb (fun i => C i y) hC_orth]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.metricDoubleTraceFibFixedFrame_frame_independent
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.metricDoubleTraceFibFixedFrame_frame_independent target :: scope.openDecls } }

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    in
private lemma metricDoubleTraceFib_eq_fixedFrame_smoothOrthoFrame_on_neighborhood
    (g : SmoothRiemannianMetric I M) (r t : ℕ) (x₀ : M)
    {y : M} (hy : y ∈ smoothOrthoFrameNeighborhood (I := I) (M := M) x₀) :
    metricDoubleTraceFib (I := I) (M := M) g r t y =
      metricDoubleTraceFibFixedFrame (I := I) (M := M) r t (smoothOrthoFrame (I := I) g x₀) y := by
  rw [metricDoubleTraceFib_eq_fixedFrame_moving]
  exact metricDoubleTraceFibFixedFrame_frame_independent (I := I) (M := M) g r t y
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g y i j)
    (fun i j => smoothOrthoFrame_orthonormal (I := I) g x₀ hy i j)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.metricDoubleTraceFib_eq_fixedFrame_smoothOrthoFrame_on_neighborhood
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.metricDoubleTraceFib_eq_fixedFrame_smoothOrthoFrame_on_neighborhood target :: scope.openDecls } }

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
omit [T2Space M] in
private lemma metricDoubleTraceFib_eventuallyEq_fixedFrame
    (g : SmoothRiemannianMetric I M) (r t : ℕ) (x₀ : M) :
    (fun x : M => TotalSpace.mk'
        (TensorRSModel r (t + 2) ℝ E →L[ℝ] TensorRSModel r t ℝ E)
        (E := fun z : M => TensorRSSpace r (t + 2) I z →L[ℝ] TensorRSSpace r t I z) x
        (metricDoubleTraceFib (I := I) (M := M) g r t x)) =ᶠ[𝓝 x₀]
      (fun x : M => TotalSpace.mk'
        (TensorRSModel r (t + 2) ℝ E →L[ℝ] TensorRSModel r t ℝ E)
        (E := fun z : M => TensorRSSpace r (t + 2) I z →L[ℝ] TensorRSSpace r t I z) x
        (metricDoubleTraceFibFixedFrame (I := I) (M := M) r t
          (smoothOrthoFrame (I := I) g x₀) x)) := by
  filter_upwards [smoothOrthoFrameNeighborhood_mem_nhds (I := I) (M := M) x₀] with y hy
  exact congrArg (TotalSpace.mk' (TensorRSModel r (t + 2) ℝ E →L[ℝ] TensorRSModel r t ℝ E)
    (E := fun z : M => TensorRSSpace r (t + 2) I z →L[ℝ] TensorRSSpace r t I z) y)
    (metricDoubleTraceFib_eq_fixedFrame_smoothOrthoFrame_on_neighborhood (I := I) (M := M) g r t x₀ hy)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.metricDoubleTraceFib_eventuallyEq_fixedFrame
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.metricDoubleTraceFib_eventuallyEq_fixedFrame target :: scope.openDecls } }

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
  private theorem metricDoubleTraceFib_contMDiffAt
    (g : SmoothRiemannianMetric I M) (r t : ℕ) (x₀ : M) :
    ContMDiffAt I
      (I.prod 𝓘(ℝ, TensorRSModel r (t + 2) ℝ E →L[ℝ] TensorRSModel r t ℝ E)) ∞
      (fun x : M => TotalSpace.mk'
        (TensorRSModel r (t + 2) ℝ E →L[ℝ] TensorRSModel r t ℝ E)
        (E := fun z : M => TensorRSSpace r (t + 2) I z →L[ℝ] TensorRSSpace r t I z) x
      (metricDoubleTraceFib (I := I) (M := M) g r t x)) x₀ := by
  have h_fixed_at :=
    metricDoubleTraceFibFixedFrame_contMDiff (I := I) (M := M) r t
      (fun i => smoothOrthoFrame_smooth (I := I) g x₀ i) x₀
  exact h_fixed_at.congr_of_eventuallyEq
    (metricDoubleTraceFib_eventuallyEq_fixedFrame (I := I) (M := M) g r t x₀)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.metricDoubleTraceFib_contMDiffAt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.metricDoubleTraceFib_contMDiffAt target :: scope.openDecls } }

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
private theorem metricDoubleTraceFib_contMDiff (g : SmoothRiemannianMetric I M) (r t : ℕ) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (t + 2) ℝ E →L[ℝ] TensorRSModel r t ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r (t + 2) ℝ E →L[ℝ] TensorRSModel r t ℝ E)
        (E := fun z : M => TensorRSSpace r (t + 2) I z →L[ℝ] TensorRSSpace r t I z) x
        (metricDoubleTraceFib (I := I) (M := M) g r t x)) :=
  fun x₀ => metricDoubleTraceFib_contMDiffAt (I := I) (M := M) g r t x₀

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.metricDoubleTraceFib_contMDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.metricDoubleTraceFib_contMDiff target :: scope.openDecls } }

noncomputable def metricDoubleTraceField (g : SmoothRiemannianMetric I M) (r : ℕ) :
    (t : ℕ) → HomTensorRSField (E := E) (M := M) r (t + 2) t I :=
  fun t =>
    { toFun := fun x : M => metricDoubleTraceFib (I := I) (M := M) g r t x
      contMDiff_toFun := metricDoubleTraceFib_contMDiff (I := I) (M := M) g r t }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metricDoubleTraceField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metricDoubleTraceField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metricDoubleTraceField ``Submission.DifferentialGeometry.Geometry.Curvature.metricDoubleTraceField

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
lemma metricDoubleTraceField_apply (g : SmoothRiemannianMetric I M) (r t : ℕ) (x : M) :
    (show TensorRSSpace r (t + 2) I x →L[ℝ] TensorRSSpace r t I x from
        metricDoubleTraceField (I := I) (M := M) (E := E) g r t x) =
      metricDoubleTraceFib (I := I) (M := M) g r t x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metricDoubleTraceField_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metricDoubleTraceField_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metricDoubleTraceField_apply ``Submission.DifferentialGeometry.Geometry.Curvature.metricDoubleTraceField_apply

theorem roughLap_eq_metricDoubleTrace (g : SmoothRiemannianMetric I M) (r t : ℕ)
    (W : SmoothCcTensor g r t) :
    rawTensorConnLapSmooth (I := I) g r t W =
      homTensorRSFieldApply (I := I) (M := M) g r (t + 2) t
        (metricDoubleTraceField (I := I) (M := M) (E := E) g r t)
        (iteratedCovGrad g r t 2 W) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [rawTensorConnLapSmooth_toSection_apply, homTensorRSFieldApply_toSection, metricDoubleTraceField_apply,
    metricDoubleTraceFib_apply]
  rw [rawTensorConnLap_eq_frame_trace_secondCovDeriv (I := I) g r t (fun z : M => W.toSection z) x]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  apply tensorRS_eq_of_eval_eq (I := I) (M := M)
  intro D m
  rw [twoSlotPeel_eval (I := I) (M := M) r t x ((iteratedCovGrad g r t 2 W).toSection x)
    (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x i x) D m]
  rw [show (iteratedCovGrad g r t 2 W).toSection x =
      (covGrad (I := I) (M := M) g r (t + 1)
        (covGrad (I := I) (M := M) g r t W)).toSection x from rfl]
  exact (secondCovGrad_eval_eq_tensorSecondCovDeriv (I := I) g r t W
    (smoothOrthoFrame_smooth (I := I) g x i) (smoothOrthoFrame_smooth (I := I) g x i) x D m).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.roughLap_eq_metricDoubleTrace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.roughLap_eq_metricDoubleTrace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.roughLap_eq_metricDoubleTrace ``Submission.DifferentialGeometry.Geometry.Curvature.roughLap_eq_metricDoubleTrace

end Curvature
end Geometry
end DifferentialGeometry
