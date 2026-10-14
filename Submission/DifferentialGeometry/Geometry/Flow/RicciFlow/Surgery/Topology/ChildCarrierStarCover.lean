import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildParent
import Submission.DifferentialGeometry.Topology.VanKampen.SimplyConnectedStarCover

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open _root_.Submission.DifferentialGeometry.Topology.VanKampen in
theorem child_simplyConnected_of_starCover {P Q D N : OrientedThreeStage.{u}}
    (E : SmoothCutCapTransition P Q D N) (c : ConnectedComponents Q.Carrier)
    (U : Set (E.ChildCarrier c)) (V : E.ChildCapBoundary c → Set (E.ChildCarrier c))
    (hU : IsOpen U) (hV : ∀ b, IsOpen (V b))
    (hcover : U ∪ ⋃ b, V b = _root_.Set.univ)
    (hdisj : Pairwise fun b b' => Disjoint (V b) (V b'))
    [hUsc : SimplyConnectedSpace ↥U] [hVsc : ∀ b, SimplyConnectedSpace ↥(V b)]
    [hInt : ∀ b, SimplyConnectedSpace ↥(U ∩ V b)] :
    SimplyConnectedSpace (Q.component c).Carrier :=
  @simplyConnectedSpace_of_open_cover_of_pairwise_disjoint_of_fintype
    (E.ChildCarrier c) _ (E.ChildCapBoundary c) _ U V hU hV hcover hdisj
    hUsc hVsc hInt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.child_simplyConnected_of_starCover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.child_simplyConnected_of_starCover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.child_simplyConnected_of_starCover ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.child_simplyConnected_of_starCover

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
