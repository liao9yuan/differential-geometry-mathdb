import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapRegionStructure

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology (ThreeSpace)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {eps : ℝ} {x : M} {t a b : ℝ}

def OrderedNeckChain.singleInterval (nk : StrongNeck S eps x t)
    (hab : a < b) (ha : -eps⁻¹ < a) (hb : b < eps⁻¹) :
    OrderedNeckChain S eps t (nk.map '' (_root_.Set.univ ×ˢ _root_.Set.Icc a b)) where
  count := 1
  count_pos := by norm_num
  centers := fun _ => x
  necks := fun _ => nk
  lo := fun _ => a
  hi := fun _ => b
  lo_lt_hi := fun _ => hab
  inside := fun _ y hy => nk.domain ⟨hy.1, ha.trans_le hy.2.1, hy.2.2.trans_lt hb⟩
  swept_eq := (_root_.Set.iUnion_const _).symm
  transition_increasing := by intro i j hij; simp at hij

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.OrderedNeckChain.singleInterval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.OrderedNeckChain.singleInterval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.OrderedNeckChain.singleInterval ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.OrderedNeckChain.singleInterval

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
