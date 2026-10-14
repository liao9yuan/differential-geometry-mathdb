import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalCurvatureBound
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CutCoreSelection

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Neck
open _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ}

theorem nonempty_cut_or_discardedCore_of_singularEndpoint
    (G : P.IncomingSlab a s) (hG : G.SingularEndpoint)
    {ι : Type*} {δ : ι → ℝ} (f : ∀ i, bufferedCylinder (δ i) → P.Carrier)
    (R : Set (ConnectedComponents (cutCore f)))
    (hRet : _root_.Set.MapsTo (Subtype.val : cutCore f → P.Carrier) (retainedCore f R) G.terminalRegularRegion) :
    Nonempty ι ∨ Nonempty (discardedCore f R) := by
  classical
  by_cases hi : Nonempty ι
  · exact Or.inl hi
  · right
    let : IsEmpty ι := not_nonempty_iff.mp hi
    have hnot := G.terminalRegularRegion_ne_univ_of_singularEndpoint hG
    obtain ⟨x, hx⟩ : ∃ x : P.Carrier, x ∉ G.terminalRegularRegion := by
      by_contra h
      apply hnot
      ext x
      simp only [_root_.Set.mem_univ, iff_true]
      exact not_exists_not.mp h x
    have hcore : x ∈ cutCore f := by
      simp only [cutCore, _root_.Set.iUnion_of_empty, _root_.Set.compl_empty, _root_.Set.mem_univ]
    let p : cutCore f := ⟨x, hcore⟩
    have hn : p ∉ retainedCore f R := fun hp => hx (hRet hp)
    exact ⟨⟨p, hn⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.nonempty_cut_or_discardedCore_of_singularEndpoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.nonempty_cut_or_discardedCore_of_singularEndpoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.nonempty_cut_or_discardedCore_of_singularEndpoint ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.nonempty_cut_or_discardedCore_of_singularEndpoint

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
