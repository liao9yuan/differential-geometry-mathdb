import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HurewiczCube
import Submission.DifferentialGeometry.Topology.Homology.HurewiczLowDegreeAssembly
import Submission.DifferentialGeometry.Topology.Homology.CubeSphereGenerator
import Submission.DifferentialGeometry.Topology.Homotopy.ManifoldVanishing

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology _root_.Set
open scoped _root_.Topology _root_.unitInterval _root_.Simplicial _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [hT2 : T2Space M] [hCompact : CompactSpace M]
    [hConnected : ConnectedSpace M] [hSimplyConnected : SimplyConnectedSpace M]

include hT2 hCompact hSimplyConnected
omit hConnected

theorem rfs_homotopy_groups (q : M) :
    Subsingleton (HomotopyGroup (Fin 2) M q) ∧ Function.Bijective (hurewiczThree q) := by
  have htwo : Subsingleton (HomotopyGroup (Fin 2) M q) :=
    DifferentialGeometry.Topology.homotopyGroup_two_subsingleton_of_simplyConnected_of_finrank_eq_three
      (E := ThreeSpace) (by simp [ThreeSpace]) q
  exact ⟨htwo,
    DifferentialGeometry.Topology.hurewiczThree_bijective_of_sphereHurewiczThreeCanonical
      q htwo DifferentialGeometry.Topology.cubeSphereFundamentalClass_isSphereHomologyGenerator
      DifferentialGeometry.Topology.sphereHurewiczThreeCanonical_of_hurewicz_three_isomorphism⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfs_homotopy_groups then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfs_homotopy_groups"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfs_homotopy_groups ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfs_homotopy_groups

def positiveHurewiczEquiv (q : M) :
    HomotopyGroup (Fin 3) M q ≃* Multiplicative (IntegralHomology M 3) :=
  MulEquiv.ofBijective (hurewiczThreeHom q) (rfs_homotopy_groups q).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.positiveHurewiczEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.positiveHurewiczEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.positiveHurewiczEquiv ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.positiveHurewiczEquiv

theorem exists_unique_positiveHomotopyClass (o : TangentOrientationSection M) (q : M) :
    ∃! alpha : HomotopyGroup (Fin 3) M q,
      hurewiczThree q alpha = fundamentalClass o := by
  exact (rfs_homotopy_groups q).2.existsUnique _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_unique_positiveHomotopyClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_unique_positiveHomotopyClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_unique_positiveHomotopyClass ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_unique_positiveHomotopyClass

def positiveHomotopyClass (o : TangentOrientationSection M) (q : M) :
    HomotopyGroup (Fin 3) M q :=
  Classical.choose (exists_unique_positiveHomotopyClass o q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.positiveHomotopyClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.positiveHomotopyClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.positiveHomotopyClass ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.positiveHomotopyClass

theorem positiveHomotopyClass_hurewicz (o : TangentOrientationSection M) (q : M) :
    hurewiczThree q (positiveHomotopyClass o q) = fundamentalClass o :=
  (Classical.choose_spec (exists_unique_positiveHomotopyClass o q)).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.positiveHomotopyClass_hurewicz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.positiveHomotopyClass_hurewicz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.positiveHomotopyClass_hurewicz ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.positiveHomotopyClass_hurewicz


include hConnected

theorem positiveHomotopyClass_infiniteOrder (o : TangentOrientationSection M) (q : M) :
    Function.Injective (fun z : ℤ => positiveHomotopyClass o q ^ z) := by
  intro m n h
  apply (fundamentalClass_generator o).injective
  simpa only [hurewiczThree_zpow, positiveHomotopyClass_hurewicz] using
    congrArg (hurewiczThree q) h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.positiveHomotopyClass_infiniteOrder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.positiveHomotopyClass_infiniteOrder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.positiveHomotopyClass_infiniteOrder ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.positiveHomotopyClass_infiniteOrder

variable {N : Type u} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
    [IsManifold ThreeModel ∞ N] [T2Space N] [CompactSpace N]
    [ConnectedSpace N] [SimplyConnectedSpace N]

omit hConnected in
theorem rfs_degree_class_transport (oM : TangentOrientationSection M)
    (oN : TangentOrientationSection N) (f : C(M, N)) (p : M) :
    basedHomotopyMap f p (positiveHomotopyClass oM p) =
      positiveHomotopyClass oN (f p) ^ orientedDegree oM oN f := by
  apply (rfs_homotopy_groups (f p)).2.injective
  rw [hurewiczThree_natural, positiveHomotopyClass_hurewicz, orientedDegree_spec,
    hurewiczThree_zpow, positiveHomotopyClass_hurewicz]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfs_degree_class_transport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfs_degree_class_transport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfs_degree_class_transport ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfs_degree_class_transport

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
