import Submission.DifferentialGeometry.Topology.ThreeManifold.PoincareStandard
import Submission.DifferentialGeometry.Topology.ThreeManifold.PoincareStandardOriented
import Submission.DifferentialGeometry.Topology.ThreeManifold.CutCapReconstruction
import Submission.DifferentialGeometry.Topology.ThreeManifold.SphericalSpaceFormTrivial
import Submission.DifferentialGeometry.Topology.FundamentalGroup.SphericalQuotient
import Submission.DifferentialGeometry.Topology.FundamentalGroup.Sphere
import Submission.DifferentialGeometry.Topology.FundamentalGroup.HomotopyEquiv
import Submission.DifferentialGeometry.Topology.Algebra.Group.FreeProduct
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology

universe u

theorem exists_diffeomorph_standardThreeSphere_of_isPoincareStandard
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [SimplyConnectedSpace M] (h : isPoincareStandard M) :
    Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ standardThreeSphereLift.{u}.Carrier) := by
  classical
  obtain ⟨P⟩ := h
  let x : (i : Fin P.factors.length) → (P.factors.get i).Carrier :=
    fun i => Classical.choice (inferInstance : Nonempty (P.factors.get i).Carrier)
  let y : (finiteConnectedSum P.factors).Carrier := Classical.choice inferInstance
  have hbase : Subsingleton (FundamentalGroup (finiteConnectedSum P.factors).Carrier y) := by
    have he : FundamentalGroup (finiteConnectedSum P.factors).Carrier y ≃*
        FundamentalGroup M (P.diffeomorph.symm y) :=
      fundamentalGroupMulEquivOfHomotopyEquiv P.diffeomorph.symm.toHomeomorph.toHomotopyEquiv
        y (P.diffeomorph.symm y) rfl
    exact he.subsingleton
  have hcoprod : Subsingleton (Monoid.CoprodI (fun i : Fin P.factors.length =>
      FundamentalGroup (P.factors.get i).Carrier (x i))) :=
    @Equiv.subsingleton _ _
      ((fundamentalGroup_finiteConnectedSum_freeProduct P.factors x y).some.symm : _ ≃ _) hbase
  have hsub : ∀ i : Fin P.factors.length,
      Subsingleton (FundamentalGroup (P.factors.get i).Carrier (x i)) :=
    (DifferentialGeometry.Algebra.Group.coprodI_subsingleton_iff _).mp hcoprod
  have hL : ∀ F ∈ P.factors, Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      F.toClosedOrientedManifold standardThreeSphereLift.{u}.toClosedOrientedManifold) := by
    intro F hF
    obtain ⟨i, rfl⟩ := List.get_of_mem hF
    exact exists_orientedDiffeomorph_standardThreeSphere_of_isStandardFactor
      (P.factors.get i) (x i) (P.standard _ hF) (hsub i)
  obtain ⟨s⟩ := exists_diffeomorph_finiteConnectedSum_standardThreeSphere P.factors hL
  exact ⟨P.diffeomorph.trans s⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_diffeomorph_standardThreeSphere_of_isPoincareStandard then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_diffeomorph_standardThreeSphere_of_isPoincareStandard"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_diffeomorph_standardThreeSphere_of_isPoincareStandard ``Submission.DifferentialGeometry.Topology.exists_diffeomorph_standardThreeSphere_of_isPoincareStandard

def poincareStandardConnectedSumClosed : Prop :=
  ∀ M N : ConnectedClosedOrientedManifold.{u} 3,
    isPoincareStandard M.Carrier → isPoincareStandard N.Carrier →
      isPoincareStandard (connectedSum M N).Carrier

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.poincareStandardConnectedSumClosed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.poincareStandardConnectedSumClosed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.poincareStandardConnectedSumClosed ``Submission.DifferentialGeometry.Topology.poincareStandardConnectedSumClosed

theorem isPoincareStandard_connectedSum_of_standardFactor
    (M N : ConnectedClosedOrientedManifold.{u} 3)
    (hM : isStandardFactor M) (hN : isStandardFactor N) :
    isPoincareStandard (connectedSum M N).Carrier := by
  have h := isPoincareStandard_finite_sum [M, N] (by
    intro F hF
    rcases List.mem_cons.mp hF with rfl | hF
    · exact hM
    rcases List.mem_cons.mp hF with rfl | hF
    · exact hN
    exact absurd hF (by simp))
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isPoincareStandard_connectedSum_of_standardFactor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isPoincareStandard_connectedSum_of_standardFactor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isPoincareStandard_connectedSum_of_standardFactor ``Submission.DifferentialGeometry.Topology.isPoincareStandard_connectedSum_of_standardFactor

theorem poincareStandardSumClosed_of_connectedSumClosed
    (h : poincareStandardConnectedSumClosed.{u}) :
    poincareStandardSumClosed.{u} := by
  intro L hL
  induction L with
  | nil => exact isPoincareStandard_sphere
  | cons M L ih =>
    cases L with
    | nil => exact hL M (by simp)
    | cons N L =>
      have hM : isPoincareStandard M.Carrier := hL M (by simp)
      have hT : isPoincareStandard (finiteConnectedSum (N :: L)).Carrier :=
        ih fun F hF => hL F (by simp [hF])
      exact h M (finiteConnectedSum (N :: L)) hM hT

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.poincareStandardSumClosed_of_connectedSumClosed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.poincareStandardSumClosed_of_connectedSumClosed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.poincareStandardSumClosed_of_connectedSumClosed ``Submission.DifferentialGeometry.Topology.poincareStandardSumClosed_of_connectedSumClosed

theorem connectedSumClosed_of_poincareStandardSumClosed
    (h : poincareStandardSumClosed.{u}) :
    poincareStandardConnectedSumClosed.{u} := by
  intro M N hM hN
  have h2 := h [M, N] (by
    intro F hF
    rcases List.mem_cons.mp hF with rfl | hF
    · exact hM
    rcases List.mem_cons.mp hF with rfl | hF
    · exact hN
    exact absurd hF (by simp))
  exact h2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.connectedSumClosed_of_poincareStandardSumClosed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.connectedSumClosed_of_poincareStandardSumClosed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.connectedSumClosed_of_poincareStandardSumClosed ``Submission.DifferentialGeometry.Topology.connectedSumClosed_of_poincareStandardSumClosed

theorem poincareStandardSumClosed_iff_connectedSumClosed :
    poincareStandardSumClosed.{u} ↔ poincareStandardConnectedSumClosed.{u} :=
  ⟨connectedSumClosed_of_poincareStandardSumClosed,
    poincareStandardSumClosed_of_connectedSumClosed⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.poincareStandardSumClosed_iff_connectedSumClosed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.poincareStandardSumClosed_iff_connectedSumClosed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.poincareStandardSumClosed_iff_connectedSumClosed ``Submission.DifferentialGeometry.Topology.poincareStandardSumClosed_iff_connectedSumClosed

end DifferentialGeometry.Topology
