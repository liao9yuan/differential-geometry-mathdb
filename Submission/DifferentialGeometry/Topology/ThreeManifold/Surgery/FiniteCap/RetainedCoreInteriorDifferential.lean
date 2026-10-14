import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCoreSmoothEmbedding
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.RetainedCoreDomainSmooth
import Submission.DifferentialGeometry.Topology.Manifold.OpenSubtypeDifferential

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Topology.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev RetInteriorDE3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.RetInteriorDE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.RetInteriorDE3 target :: scope.openDecls } }
private abbrev RetInteriorDE2 := EuclideanSpace ℝ (Fin 2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.RetInteriorDE2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.RetInteriorDE2 target :: scope.openDecls } }
private abbrev RetInteriorDIR := (𝓡 2).prod (𝓡∂ 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.RetInteriorDIR
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.RetInteriorDIR target :: scope.openDecls } }
private abbrev RetInteriorDIC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.RetInteriorDIC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.RetInteriorDIC target :: scope.openDecls } }
private abbrev RetInteriorDIH := ModelProd RetInteriorDE2 (EuclideanHalfSpace 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.RetInteriorDIH
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.RetInteriorDIH target :: scope.openDecls } }
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ} {L : ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph RetInteriorDIC I ∞ (f i))
local notation "RetInteriorDQ" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

include hs in
theorem finiteRetainedCoreInclusion_mfderiv_interior
    (R : Set (ConnectedComponents (cutCore f))) (U : _root_.TopologicalSpace.Opens M)
    (hRet : _root_.Set.MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U)
    (p : retainedCore f R) (hp : p.val.val ∈ interior (cutCore f)) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace RetInteriorDIH (retainedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj R
    let : ChartedSpace RetInteriorDE3 RetInteriorDQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    mfderiv RetInteriorDIR (𝓡 3) (finiteRetainedCoreInclusion hL hδ f hf hdisj R) p =
      (mfderiv I (𝓡 3) (finiteCoreInteriorMap hL hδ f (fun i => (hf i).injective) hdisj)
        (⟨p.val.val, hp⟩ : coreInteriorDomain f)).comp
        (mfderiv RetInteriorDIR I (retainedCoreDomainMap f R U hRet) p) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace RetInteriorDIH (retainedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj R
  let : ChartedSpace RetInteriorDE3 RetInteriorDQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let V : _root_.TopologicalSpace.Opens (retainedCore f R) :=
    ⟨{q | q.val.val ∈ interior (cutCore f)}, isOpen_interior.preimage (continuous_subtype_val.comp continuous_subtype_val)⟩
  let q : V := ⟨p, hp⟩
  let F : V → coreInteriorDomain f := fun r => ⟨r.val.val.val, r.property⟩
  let Ψ := retainedCoreDomainMap f R U hRet
  let Φ := finiteRetainedCoreInclusion hL hδ f hf hdisj R
  let Ξ := (Subtype.val : finiteCapRetained hL hδ f hf hdisj R → RetInteriorDQ) ∘ Φ
  let old := finiteCoreInteriorMap hL hδ f (fun i => (hf i).injective) hdisj
  let ambient : retainedCore f R → M := fun r => r.val.val
  have hAmb : ContMDiff RetInteriorDIR I ∞ ambient :=
    (retainedCore_ambientInclusion_isSmoothEmbedding I hdim hδ f hf hdisj R hs).contMDiff
  have hF : ContMDiff RetInteriorDIR I ∞ F :=
    (ContMDiff.subtypeVal_comp_iff (coreInteriorDomain f) F).mp
      (hAmb.comp (contMDiff_subtype_val (I := RetInteriorDIR) (U := V)))
  have hΦ : ContMDiff RetInteriorDIR (𝓡 3) ∞ Φ :=
    (finiteRetainedCoreInclusion_isSmoothEmbedding I hdim hL hδ f hf hdisj hs R).contMDiff
  have hΞ : ContMDiff RetInteriorDIR (𝓡 3) ∞ Ξ :=
    (contMDiff_subtype_val (I := 𝓡 3) (U := finiteCapRetained hL hδ f hf hdisj R)).comp hΦ
  have hOld : ContMDiff I (𝓡 3) ∞ old := contMDiff_finiteCoreInteriorMap I hdim hL hδ f hf hdisj hs
  have hFder : mfderiv RetInteriorDIR I F q = mfderiv RetInteriorDIR I Ψ p :=
    (mfderiv_comp_open_val RetInteriorDIR I (coreInteriorDomain f) F hF q).symm.trans
      ((DifferentialGeometry.mfderiv_restrict_open
          (I := RetInteriorDIR) (J := I) ambient V q).trans
        (retainedCoreDomainMap_mfderiv I hdim hδ f hf hdisj hs R U hRet p).symm)
  have hcomp : mfderiv RetInteriorDIR (𝓡 3) (Ξ ∘ (Subtype.val : V → retainedCore f R)) q =
      (mfderiv I (𝓡 3) old (F q)).comp (mfderiv RetInteriorDIR I F q) :=
    mfderiv_comp q (hOld.mdifferentiableAt (by simp)) (hF.mdifferentiableAt (by simp))
  exact (mfderiv_comp_open_val RetInteriorDIR (𝓡 3) (finiteCapRetained hL hδ f hf hdisj R) Φ hΦ p).symm.trans
    (((DifferentialGeometry.mfderiv_restrict_open
        (I := RetInteriorDIR) (J := 𝓡 3) Ξ V q).symm.trans hcomp).trans
      (congrArg ((mfderiv I (𝓡 3) old (F q)).comp) hFder))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteRetainedCoreInclusion_mfderiv_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteRetainedCoreInclusion_mfderiv_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteRetainedCoreInclusion_mfderiv_interior ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteRetainedCoreInclusion_mfderiv_interior
end DifferentialGeometry.Topology.ThreeManifold.Surgery
