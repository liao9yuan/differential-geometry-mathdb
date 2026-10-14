import Submission.DifferentialGeometry.Topology.Manifold.ProductHalfSpaceBoundary
import Submission.DifferentialGeometry.Topology.Manifold.Attachment.RadialInducedBoundaryOrientation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.Module _root_.Filter _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Topology.Manifold.Attachment
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.Manifold

theorem contMDiff_intoIntrinsicBoundary
    {E H M F K N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [hI : HasSmoothBoundary E H I] [Nonempty hI.boundaryH] [IsManifold I ∞ M]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ F K} [TopologicalSpace N] [ChartedSpace K N]
    (f : N → BoundaryManifold I M)
    (hf : ContMDiff J I ∞ (fun x => (f x : M))) : ContMDiff J hI.boundaryI ∞ f := by
  intro x
  have hc : ContinuousAt f x := (continuous_induced_rng.mpr hf.continuous).continuousAt
  rw [contMDiffAt_iff_target_of_mem_source (mem_chart_source hI.boundaryH (f x))]
  refine ⟨hc, ?_⟩
  have hext : ContMDiffAt J 𝓘(ℝ, E) ∞
      (extChartAt I (f x : M) ∘ (fun y => (f y : M))) x :=
    (contMDiffAt_extChartAt (I := I) (x := (f x : M))).comp x (hf x)
  apply (hI.projE_contDiff.contMDiff.contMDiffAt.comp x hext).congr_of_eventuallyEq
  have hevent : ∀ᶠ y in 𝓝 x, (f y : M) ∈ (chartAt H (f x : M)).source :=
    (hf x).continuousAt.eventually
      ((chartAt H (f x : M)).open_source.mem_nhds (mem_chart_source H (f x : M)))
  filter_upwards [hevent] with y hy
  change hI.boundaryI (chartAt hI.boundaryH (f x) (f y)) =
    hI.projE (I (chartAt H (f x : M) (f y : M)))
  have hchart : chartAt hI.boundaryH (f x) = BoundaryManifold.boundaryChart (I := I) (f x) :=
    BoundaryManifold.defaultBoundaryChart_eq_boundaryChart (I := I) (f x)
  rw [hchart]
  have hincl := BoundaryManifold.inclH_boundaryChart_apply (I := I) (f x) (f y) hy
  rw [← hincl]
  exact (hI.proj_inclH_compat (BoundaryManifold.boundaryChart (I := I) (f x) (f y))).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.contMDiff_intoIntrinsicBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.contMDiff_intoIntrinsicBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.contMDiff_intoIntrinsicBoundary ``Submission.DifferentialGeometry.Topology.Manifold.contMDiff_intoIntrinsicBoundary

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.E3 target :: scope.openDecls } }
private abbrev E2 := EuclideanSpace ℝ (Fin 2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.E2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.E2 target :: scope.openDecls } }
private abbrev E1 := EuclideanSpace ℝ (Fin 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.E1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.E1 target :: scope.openDecls } }
private abbrev ER := E2 × E1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.ER
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.ER target :: scope.openDecls } }
private abbrev IH := ModelProd E2 (EuclideanHalfSpace 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.IH
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.IH target :: scope.openDecls } }
private abbrev IR := (𝓡 2).prod (𝓡∂ 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.IR
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.IR target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.S2 target :: scope.openDecls } }
private abbrev Collar (B : ℝ) := S2 × _root_.Set.Ico (0 : ℝ) B

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Collar
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Collar target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.Manifold.instHasSmoothBoundaryERIHIR : HasSmoothBoundary ER IH IR := productHalfSpaceBoundaryModel

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.instHasSmoothBoundaryERIHIR
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.instHasSmoothBoundaryERIHIR target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.Manifold.instNonemptyBoundaryHProdEuclideanSpaceRealFinOfNatNatModelProdEuclideanHalfSpaceIR : Nonempty (HasSmoothBoundary.boundaryH IR) := show Nonempty E2 from inferInstance

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.instNonemptyBoundaryHProdEuclideanSpaceRealFinOfNatNatModelProdEuclideanHalfSpaceIR
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.instNonemptyBoundaryHProdEuclideanSpaceRealFinOfNatNatModelProdEuclideanHalfSpaceIR target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.Manifold.instChartedSpaceE2BoundaryManifoldProdEuclideanSpaceRealFinOfNatNatModelProdEuclideanHalfSpaceIROfIsManifoldSomeENatTop {M : Type*} [TopologicalSpace M] [ChartedSpace IH M]
    [IsManifold IR ∞ M] : ChartedSpace E2 (BoundaryManifold IR M) := BoundaryManifold.chartedSpace (I := IR)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.instChartedSpaceE2BoundaryManifoldProdEuclideanSpaceRealFinOfNatNatModelProdEuclideanHalfSpaceIROfIsManifoldSomeENatTop
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.instChartedSpaceE2BoundaryManifoldProdEuclideanSpaceRealFinOfNatNatModelProdEuclideanHalfSpaceIROfIsManifoldSomeENatTop target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.Manifold.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopBoundaryManifoldProdModelProdEuclideanHalfSpaceIR {M : Type*} [TopologicalSpace M] [ChartedSpace IH M]
    [IsManifold IR ∞ M] : IsManifold (𝓡 2) ∞ (BoundaryManifold IR M) := BoundaryManifold.isManifold (I := IR)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopBoundaryManifoldProdModelProdEuclideanHalfSpaceIR
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopBoundaryManifoldProdModelProdEuclideanHalfSpaceIR target :: scope.openDecls } }
private def nativeFaceForward {B : ℝ} (hB : 0 < B) :
    letI := halfClosedIntervalChartedSpace hB
    BoundaryManifold IR (Collar B) → retainedFace B := by
  let := halfClosedIntervalChartedSpace hB
  exact fun b => ⟨b.val, (Set.ext_iff.mp (retainedCylinder_boundary_eq hB) b.val).mp b.property⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.nativeFaceForward
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.nativeFaceForward target :: scope.openDecls } }
private def nativeFaceInverse {B : ℝ} (hB : 0 < B) :
    letI := halfClosedIntervalChartedSpace hB
    retainedFace B → BoundaryManifold IR (Collar B) := by
  let := halfClosedIntervalChartedSpace hB
  exact fun q => ⟨q.val, (Set.ext_iff.mp (retainedCylinder_boundary_eq hB) q.val).mpr q.property⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.nativeFaceInverse
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.nativeFaceInverse target :: scope.openDecls } }
private theorem nativeFaceForward_smooth {B : ℝ} (hB : 0 < B) :
    letI := halfClosedIntervalChartedSpace hB
    letI := halfClosedInterval_isManifold hB
    letI := retainedFaceChartedSpace hB
    ContMDiff (𝓡 2) (𝓡 2) ∞ (nativeFaceForward hB) := by
  let := halfClosedIntervalChartedSpace hB
  let := halfClosedInterval_isManifold hB
  let := retainedFaceChartedSpace hB
  have hp : ContMDiff (𝓡 2) (𝓡 2) ∞ (fun b : BoundaryManifold IR (Collar B) => b.val.1) :=
    contMDiff_fst.comp (boundaryInclusion_contMDiff (I := IR) (M := Collar B))
  have he : nativeFaceForward hB =
      (fun b : BoundaryManifold IR (Collar B) => retainedFaceDiffeomorph hB b.val.1) := by
    funext b
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact (nativeFaceForward hB b).property
  rw [he]
  exact (retainedFaceDiffeomorph hB).contMDiff.comp hp

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.nativeFaceForward_smooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.nativeFaceForward_smooth target :: scope.openDecls } }
private theorem nativeFaceInverse_smooth {B : ℝ} (hB : 0 < B) :
    letI := halfClosedIntervalChartedSpace hB
    letI := halfClosedInterval_isManifold hB
    letI := retainedFaceChartedSpace hB
    ContMDiff (𝓡 2) (𝓡 2) ∞ (nativeFaceInverse hB) := by
  let := halfClosedIntervalChartedSpace hB
  let := halfClosedInterval_isManifold hB
  let := retainedFaceChartedSpace hB
  exact contMDiff_intoIntrinsicBoundary (nativeFaceInverse hB) (retainedFaceInclusion_contMDiff hB)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.nativeFaceInverse_smooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.nativeFaceInverse_smooth target :: scope.openDecls } }

def retainedBoundaryFaceDiffeomorph {B : ℝ} (hB : 0 < B) :
    letI := halfClosedIntervalChartedSpace hB
    letI := halfClosedInterval_isManifold hB
    letI := retainedFaceChartedSpace hB
    BoundaryManifold IR (Collar B) ≃ₘ⟮𝓡 2, 𝓡 2⟯ retainedFace B := by
  let := halfClosedIntervalChartedSpace hB
  let := halfClosedInterval_isManifold hB
  let := retainedFaceChartedSpace hB
  exact
    { toFun := nativeFaceForward hB
      invFun := nativeFaceInverse hB
      left_inv := fun _ => by apply Subtype.ext; rfl
      right_inv := fun _ => by apply Subtype.ext; rfl
      contMDiff_toFun := nativeFaceForward_smooth hB
      contMDiff_invFun := nativeFaceInverse_smooth hB }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.retainedBoundaryFaceDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.retainedBoundaryFaceDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.retainedBoundaryFaceDiffeomorph ``Submission.DifferentialGeometry.Topology.Manifold.retainedBoundaryFaceDiffeomorph

theorem retainedBoundaryFaceDiffeomorph_apply {B : ℝ} (hB : 0 < B) :
    letI := halfClosedIntervalChartedSpace hB
    letI := halfClosedInterval_isManifold hB
    letI := retainedFaceChartedSpace hB
    ∀ b : BoundaryManifold IR (Collar B), (retainedBoundaryFaceDiffeomorph hB b).val = b.val := by
  let := halfClosedIntervalChartedSpace hB
  let := halfClosedInterval_isManifold hB
  let := retainedFaceChartedSpace hB
  intro b
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.retainedBoundaryFaceDiffeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.retainedBoundaryFaceDiffeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.retainedBoundaryFaceDiffeomorph_apply ``Submission.DifferentialGeometry.Topology.Manifold.retainedBoundaryFaceDiffeomorph_apply

theorem retainedBoundaryFaceDiffeomorph_symm_apply {B : ℝ} (hB : 0 < B) :
    letI := halfClosedIntervalChartedSpace hB
    letI := halfClosedInterval_isManifold hB
    letI := retainedFaceChartedSpace hB
    ∀ q : retainedFace B, ((retainedBoundaryFaceDiffeomorph hB).symm q).val = q.val := by
  let := halfClosedIntervalChartedSpace hB
  let := halfClosedInterval_isManifold hB
  let := retainedFaceChartedSpace hB
  intro q
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.retainedBoundaryFaceDiffeomorph_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.retainedBoundaryFaceDiffeomorph_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.retainedBoundaryFaceDiffeomorph_symm_apply ``Submission.DifferentialGeometry.Topology.Manifold.retainedBoundaryFaceDiffeomorph_symm_apply
end DifferentialGeometry.Topology.Manifold
