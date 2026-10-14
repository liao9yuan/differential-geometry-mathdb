import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventBridge
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SphericalCappingBridge
import Submission.DifferentialGeometry.Topology.Handle.Manifold
import Submission.DifferentialGeometry.Topology.Manifold.ClosedBall
import Submission.DifferentialGeometry.Topology.Manifold.SmoothEmbeddingDiffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Topology.Handle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.E3 target :: scope.openDecls } }

attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

private def ballHomeo : ThreeBall ≃ₜ DifferentialGeometry.Topology.ClosedCell 3 :=
  (closedCellBallHomeo 3).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ballHomeo
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ballHomeo target :: scope.openDecls } }

@[reducible] def threeBallChartedSpace : ChartedSpace (EuclideanHalfSpace 3) ThreeBall :=
  chartedSpaceOfHomeomorph ballHomeo

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.threeBallChartedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.threeBallChartedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.threeBallChartedSpace ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.threeBallChartedSpace

attribute [local instance] threeBallChartedSpace

theorem threeBall_isManifold : IsManifold (𝓡∂ 3) ∞ ThreeBall :=
  isManifoldOfHomeomorph (𝓡∂ 3) ballHomeo

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.threeBall_isManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.threeBall_isManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.threeBall_isManifold ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.threeBall_isManifold

attribute [local instance] threeBall_isManifold

def threeBallDiffeomorph :
    DifferentialGeometry.Topology.ClosedCell 3 ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ThreeBall where
  toEquiv := ballHomeo.symm.toEquiv
  contMDiff_toFun := contMDiff_homeomorph_symm_of_chartedSpaceOfHomeomorph ballHomeo (𝓡∂ 3) ∞
  contMDiff_invFun := contMDiff_homeomorph_of_chartedSpaceOfHomeomorph ballHomeo (𝓡∂ 3) ∞

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.threeBallDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.threeBallDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.threeBallDiffeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.threeBallDiffeomorph

theorem threeBallDiffeomorph_apply_val (x : DifferentialGeometry.Topology.ClosedCell 3) :
    (threeBallDiffeomorph x).1 = x.1 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.threeBallDiffeomorph_apply_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.threeBallDiffeomorph_apply_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.threeBallDiffeomorph_apply_val ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.threeBallDiffeomorph_apply_val

theorem threeBallDiffeomorph_symm_apply_val (x : ThreeBall) :
    (threeBallDiffeomorph.symm x).1 = x.1 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.threeBallDiffeomorph_symm_apply_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.threeBallDiffeomorph_symm_apply_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.threeBallDiffeomorph_symm_apply_val ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.threeBallDiffeomorph_symm_apply_val

theorem isSmoothEmbedding_threeBall_inclusion :
    IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ (Subtype.val : ThreeBall → ThreeSpace) := by
  have h := DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_diffeomorph_precomp
    (I := 𝓡∂ 3) (J := ThreeModel)
    (M := DifferentialGeometry.Topology.ClosedCell 3) (N := ThreeSpace) (P := ThreeBall)
    (Subtype.val : DifferentialGeometry.Topology.ClosedCell 3 → ThreeSpace)
    (DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_closedCell_inclusion 2)
    threeBallDiffeomorph.symm
  convert h using 1
  funext x
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isSmoothEmbedding_threeBall_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isSmoothEmbedding_threeBall_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isSmoothEmbedding_threeBall_inclusion ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isSmoothEmbedding_threeBall_inclusion

theorem range_sphereToThreeBall :
    Set.range sphereToThreeBall = {x : ThreeBall | ‖x.1‖ = 1} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change ‖(y : E3)‖ = 1
    simpa only [Metric.mem_sphere, dist_eq_norm, sub_zero] using y.2
  · intro hx
    change ‖(x : E3)‖ = 1 at hx
    exact ⟨⟨x.1, by simpa only [Metric.mem_sphere, dist_eq_norm, sub_zero] using hx⟩,
      Subtype.ext rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.range_sphereToThreeBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.range_sphereToThreeBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.range_sphereToThreeBall ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.range_sphereToThreeBall

theorem threeBall_boundary_eq_sphere :
    (𝓡∂ 3).boundary ThreeBall = Set.range sphereToThreeBall := by
  rw [range_sphereToThreeBall, ← threeBallDiffeomorph.image_boundary (by simp),
    DifferentialGeometry.Topology.Manifold.closedCell_boundary_eq_sphere 2]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change ‖(threeBallDiffeomorph y).1‖ = 1
    rw [threeBallDiffeomorph_apply_val]
    exact hy
  · intro hx
    change ‖(x : E3)‖ = 1 at hx
    exact ⟨⟨x.1, by rw [hx]⟩, hx, Subtype.ext rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.threeBall_boundary_eq_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.threeBall_boundary_eq_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.threeBall_boundary_eq_sphere ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.threeBall_boundary_eq_sphere

variable {M Q : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3}

theorem sphericalCutCap_capmap_eq (E : DifferentialGeometry.Topology.SphericalCutCapTransition M Q)
    (b : E.tubes.Boundary) :
    ⇑((E.capping.toTopological).cap b) =
      ⇑(E.capping.cap b) ∘ ⇑(threeBallDiffeomorph.symm :
        ThreeBall ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯
          DifferentialGeometry.Topology.ClosedCell 3) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphericalCutCap_capmap_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphericalCutCap_capmap_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphericalCutCap_capmap_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphericalCutCap_capmap_eq

theorem sphericalCutCap_subtype_eq (x : ThreeBall) :
    (Subtype.val : ThreeBall → ThreeSpace) x =
      (Subtype.val : DifferentialGeometry.Topology.ClosedCell 3 → ThreeSpace)
        (threeBallDiffeomorph.symm x) :=
  threeBallDiffeomorph_symm_apply_val x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphericalCutCap_subtype_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphericalCutCap_subtype_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphericalCutCap_subtype_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphericalCutCap_subtype_eq

theorem sphericalCutCap_cap_smooth
    (E : DifferentialGeometry.Topology.SphericalCutCapTransition M Q)
    (b : E.tubes.Boundary) :
    IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ (⇑((E.capping.toTopological).cap b)) := by
  have h := DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_diffeomorph_precomp
    (I := 𝓡∂ 3) (J := ThreeModel)
    (M := DifferentialGeometry.Topology.ClosedCell 3) (N := E.capped.Carrier) (P := ThreeBall)
    (E.capping.cap b) (E.capping.cap_embedding b) threeBallDiffeomorph.symm
  rw [sphericalCutCap_capmap_eq E b]
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphericalCutCap_cap_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphericalCutCap_cap_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphericalCutCap_cap_smooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphericalCutCap_cap_smooth

variable {P : OrientedThreeStage.{u}} {a s : ℝ}

theorem OrientedThreeStage.IncomingSlab.terminalRegularRegion_eq_univ
    (G : P.IncomingSlab a s) (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ t ∈ _root_.Set.Ico a s, ∀ y : P.Carrier, G.riemannNorm t y ≤ K) :
    G.terminalRegularRegion = univ := by
  refine _root_.Set.eq_univ_of_forall fun x =>
    ⟨univ, isOpen_univ, _root_.Set.mem_univ x, a, ⟨le_rfl, G.lt⟩, K, hK, ?_⟩
  intro y _ t ht
  exact hb t ht y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.terminalRegularRegion_eq_univ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.terminalRegularRegion_eq_univ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.terminalRegularRegion_eq_univ ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.terminalRegularRegion_eq_univ

theorem SmoothCutCapTransition.retainedTerminal_of_terminalRegularRegion_eq_univ
    {Q D N : OrientedThreeStage.{u}} {X : SmoothCutCapTransition P Q D N}
    (G : P.IncomingSlab a s) (h : G.terminalRegularRegion = _root_.Set.univ) :
    ∀ x : X.trace.tubes.core, x ∈ X.trace.retainedCore → x.1 ∈ G.terminalRegularRegion :=
  fun _ _ => by rw [h]; exact _root_.Set.mem_univ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.retainedTerminal_of_terminalRegularRegion_eq_univ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.retainedTerminal_of_terminalRegularRegion_eq_univ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.retainedTerminal_of_terminalRegularRegion_eq_univ ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.retainedTerminal_of_terminalRegularRegion_eq_univ

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
