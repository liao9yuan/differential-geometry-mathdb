import Submission.DifferentialGeometry.Topology.Connected.Components
import Submission.DifferentialGeometry.Topology.SphereSeparation.HeightLevel

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Topology.SphereSeparation

theorem natCard_connectedComponents_height_level_lt_of_range_inter_eq
    {e g : SphereTwo → EuclideanThree}
    (he : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (hg : _root_.Topology.IsEmbedding g) {c : ℝ}
    (hr : ∀ x, e x 2 = c → mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun y => e y 2) x ≠ 0)
    {D : Set SphereTwo} (hD : IsClosed D)
    (hne : (D ∩ {x | e x 2 = c}).Nonempty)
    (hlevel : _root_.Set.range g ∩ {z | z 2 = c} = e '' Dᶜ ∩ {z | z 2 = c}) :
    Nat.card (ConnectedComponents {x : SphereTwo // g x 2 = c}) <
      Nat.card (ConnectedComponents {x : SphereTwo // e x 2 = c}) := by
  let C : Set EuclideanThree := {z | z 2 = c}
  have hC : IsClosed C := isClosed_eq (EuclideanSpace.proj 2).continuous continuous_const
  let : Finite (ConnectedComponents (e ⁻¹' C)) :=
    (exists_source_height_level_circles he c hr).1
  exact he.isEmbedding.natCard_connectedComponents_preimage_lt_of_range_inter_eq
    hg ((isCompact_range hg.continuous).inter_right hC).isClosed hD hne hlevel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.natCard_connectedComponents_height_level_lt_of_range_inter_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.natCard_connectedComponents_height_level_lt_of_range_inter_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.natCard_connectedComponents_height_level_lt_of_range_inter_eq ``Submission.DifferentialGeometry.Topology.SphereSeparation.natCard_connectedComponents_height_level_lt_of_range_inter_eq

end DifferentialGeometry.Topology.SphereSeparation
