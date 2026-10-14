import Submission.DifferentialGeometry.Topology.Manifold.NativeRetainedBoundary

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.Module _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.Manifold
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
variable {M N : Type*} [TopologicalSpace M] [ChartedSpace IH M] [IsManifold IR ∞ M]
variable [TopologicalSpace N] [ChartedSpace IH N] [IsManifold IR ∞ N]

def productBoundaryMap (f : M → N) (hf : IsLocalDiffeomorph IR IR ∞ f) :
    BoundaryManifold IR M → BoundaryManifold IR N :=
  fun b => ⟨f b.val, ((hf b.val).isBoundaryPoint_iff (by simp)).mp b.property⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.productBoundaryMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.productBoundaryMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.productBoundaryMap ``Submission.DifferentialGeometry.Topology.Manifold.productBoundaryMap

omit [IsManifold IR ∞ M] [IsManifold IR ∞ N] in
theorem productBoundaryMap_apply (f : M → N) (hf : IsLocalDiffeomorph IR IR ∞ f) (b : BoundaryManifold IR M) :
    (productBoundaryMap f hf b).val = f b.val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.productBoundaryMap_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.productBoundaryMap_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.productBoundaryMap_apply ``Submission.DifferentialGeometry.Topology.Manifold.productBoundaryMap_apply

theorem productBoundaryMap_contMDiff (f : M → N) (hf : IsLocalDiffeomorph IR IR ∞ f) :
    ContMDiff (𝓡 2) (𝓡 2) ∞ (productBoundaryMap f hf) :=
  contMDiff_intoIntrinsicBoundary (productBoundaryMap f hf)
    (hf.contMDiff.comp (boundaryInclusion_contMDiff (I := IR) (M := M)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.productBoundaryMap_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.productBoundaryMap_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.productBoundaryMap_contMDiff ``Submission.DifferentialGeometry.Topology.Manifold.productBoundaryMap_contMDiff

private def sourceInclusionDerivative (b : BoundaryManifold IR M) : E2 →L[ℝ] ER :=
  mfderiv (𝓡 2) IR (boundaryInclusion IR M) b

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.sourceInclusionDerivative
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.sourceInclusionDerivative target :: scope.openDecls } }
private def targetInclusionDerivative (b : BoundaryManifold IR N) : E2 →L[ℝ] ER :=
  mfderiv (𝓡 2) IR (boundaryInclusion IR N) b

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.targetInclusionDerivative
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.targetInclusionDerivative target :: scope.openDecls } }
private def ambientDerivative (f : M → N) (b : BoundaryManifold IR M) : ER →L[ℝ] ER :=
  mfderiv IR IR f b.val

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.ambientDerivative
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.ambientDerivative target :: scope.openDecls } }
private def restrictedDerivative (f : M → N) (hf : IsLocalDiffeomorph IR IR ∞ f)
    (b : BoundaryManifold IR M) : E2 →L[ℝ] E2 :=
  mfderiv (𝓡 2) (𝓡 2) (productBoundaryMap f hf) b

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.restrictedDerivative
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.restrictedDerivative target :: scope.openDecls } }

theorem productBoundaryMap_mfderiv_chain (f : M → N) (hf : IsLocalDiffeomorph IR IR ∞ f)
    (b : BoundaryManifold IR M) :
    let DN : E2 →L[ℝ] ER := mfderiv (𝓡 2) IR (boundaryInclusion IR N) (productBoundaryMap f hf b)
    let DB : E2 →L[ℝ] E2 := mfderiv (𝓡 2) (𝓡 2) (productBoundaryMap f hf) b
    let DF : ER →L[ℝ] ER := mfderiv IR IR f b.val
    let DM : E2 →L[ℝ] ER := mfderiv (𝓡 2) IR (boundaryInclusion IR M) b
    DN.comp DB = DF.comp DM := by
  have hN := mfderiv_comp b ((boundaryInclusion_contMDiff (I := IR) (M := N)).mdifferentiableAt (by simp))
    ((productBoundaryMap_contMDiff f hf).mdifferentiableAt (by simp))
  have hM := mfderiv_comp b (hf.contMDiff.mdifferentiableAt (by simp))
    ((boundaryInclusion_contMDiff (I := IR) (M := M)).mdifferentiableAt (by simp))
  exact hN.symm.trans hM

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.productBoundaryMap_mfderiv_chain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.productBoundaryMap_mfderiv_chain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.productBoundaryMap_mfderiv_chain ``Submission.DifferentialGeometry.Topology.Manifold.productBoundaryMap_mfderiv_chain

theorem productBoundaryMap_mfderiv_bijective (f : M → N) (hf : IsLocalDiffeomorph IR IR ∞ f)
    (b : BoundaryManifold IR M) :
    Bijective (mfderiv (𝓡 2) (𝓡 2) (productBoundaryMap f hf) b) := by
  have hchain : (targetInclusionDerivative (productBoundaryMap f hf b)).comp (restrictedDerivative f hf b) =
      (ambientDerivative f b).comp (sourceInclusionDerivative b) := productBoundaryMap_mfderiv_chain f hf b
  have hsrc : _root_.Function.Injective (sourceInclusionDerivative b) := dincl_injective (I := IR) b
  have hamb : _root_.Function.Injective (ambientDerivative f b) := ((hf b.val).mfderivToContinuousLinearEquiv (by simp)).injective
  have hbij : _root_.Function.Injective (restrictedDerivative f hf b) := by
    intro v w hvw
    apply hsrc
    apply hamb
    have hv := congrArg (fun D : E2 →L[ℝ] ER => D v) hchain
    have hw := congrArg (fun D : E2 →L[ℝ] ER => D w) hchain
    exact hv.symm.trans ((congrArg (targetInclusionDerivative (productBoundaryMap f hf b)) hvw).trans hw)
  exact (restrictedDerivative f hf b).toLinearMap.linearEquivOfInjective hbij rfl |>.bijective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.productBoundaryMap_mfderiv_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.productBoundaryMap_mfderiv_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.productBoundaryMap_mfderiv_bijective ``Submission.DifferentialGeometry.Topology.Manifold.productBoundaryMap_mfderiv_bijective
end DifferentialGeometry.Topology.Manifold
