import Submission.DifferentialGeometry.Topology.Covering.FiniteFundamentalGroup
import Submission.DifferentialGeometry.Topology.FundamentalGroup.Sphere
import Submission.DifferentialGeometry.Topology.Manifold.OpenSphereCylinder

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Metric _root_.Manifold
open scoped _root_.ContDiff _root_.ContinuousMap

namespace DifferentialGeometry.Topology

theorem simplyConnectedSpace_sphereTwo_prod_real : SimplyConnectedSpace (SphereTwo × ℝ) := by
  let e : SphereTwo × ℝ ≃ₕ SphereTwo :=
    ((ContinuousMap.HomotopyEquiv.refl SphereTwo).prodCongr
      (ContractibleSpace.hequiv_unit ℝ).some).trans
        (Homeomorph.prodUnique SphereTwo Unit).toHomotopyEquiv
  exact e.simplyConnectedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.simplyConnectedSpace_sphereTwo_prod_real then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.simplyConnectedSpace_sphereTwo_prod_real"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.simplyConnectedSpace_sphereTwo_prod_real ``Submission.DifferentialGeometry.Topology.simplyConnectedSpace_sphereTwo_prod_real

inductive cylinderDeckModel
  | trivial
  | antipodal
  | twisted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cylinderDeckModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cylinderDeckModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cylinderDeckModel ``Submission.DifferentialGeometry.Topology.cylinderDeckModel

namespace cylinderDeckModel

def transform : cylinderDeckModel → SphereTwo × ℝ → SphereTwo × ℝ
  | trivial, q => q
  | antipodal, q => (-q.1, q.2)
  | twisted, q => (-q.1, -q.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cylinderDeckModel.transform then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cylinderDeckModel.transform"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cylinderDeckModel.transform ``Submission.DifferentialGeometry.Topology.cylinderDeckModel.transform

def rel : cylinderDeckModel → SphereTwo × ℝ → SphereTwo × ℝ → Prop
  | trivial, q, r => q = r
  | antipodal, q, r => q = r ∨ r = (-q.1, q.2)
  | twisted, q, r => q = r ∨ r = (-q.1, -q.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cylinderDeckModel.rel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cylinderDeckModel.rel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cylinderDeckModel.rel ``Submission.DifferentialGeometry.Topology.cylinderDeckModel.rel

theorem mem_pair_of_rel (d : cylinderDeckModel) {q r : SphereTwo × ℝ}
    (h : d.rel q r) : r ∈ ({q, d.transform q} : Set (SphereTwo × ℝ)) := by
  cases d <;> simp only [rel, transform] at h ⊢
  · exact Or.inl h.symm
  · exact h.imp Eq.symm id
  · exact h.imp Eq.symm id

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cylinderDeckModel.mem_pair_of_rel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cylinderDeckModel.mem_pair_of_rel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cylinderDeckModel.mem_pair_of_rel ``Submission.DifferentialGeometry.Topology.cylinderDeckModel.mem_pair_of_rel

end cylinderDeckModel

structure smoothCylinderCover (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] where
  projection : SphereTwo × ℝ → M
  isCoveringMap : IsCoveringMap projection
  surjective : Function.Surjective projection
  isLocalDiffeomorph :
    IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) ∞ projection
  deckModel : cylinderDeckModel
  fiber_iff : ∀ q r, projection q = projection r ↔ deckModel.rel q r

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.smoothCylinderCover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.smoothCylinderCover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.smoothCylinderCover ``Submission.DifferentialGeometry.Topology.smoothCylinderCover

namespace smoothCylinderCover

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

theorem finite_fiber (c : smoothCylinderCover M) (x : M) :
    Finite (c.projection ⁻¹' {x}) := by
  obtain ⟨q, hq⟩ := c.surjective x
  have hsub : c.projection ⁻¹' {x} ⊆ ({q, c.deckModel.transform q} : Set (SphereTwo × ℝ)) := by
    intro r hr
    exact c.deckModel.mem_pair_of_rel ((c.fiber_iff q r).mp (hq.trans hr.symm))
  exact ((Set.finite_singleton (c.deckModel.transform q)).insert q).subset hsub

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.smoothCylinderCover.finite_fiber then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.smoothCylinderCover.finite_fiber"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.smoothCylinderCover.finite_fiber ``Submission.DifferentialGeometry.Topology.smoothCylinderCover.finite_fiber

theorem finite_fundamentalGroup (c : smoothCylinderCover M) (x : M) :
    Finite (FundamentalGroup M x) := by
  let : SimplyConnectedSpace (SphereTwo × ℝ) := simplyConnectedSpace_sphereTwo_prod_real
  let : Finite (c.projection ⁻¹' {x}) := c.finite_fiber x
  obtain ⟨q, hq⟩ := c.surjective x
  exact finite_fundamentalGroup_of_finite_fiber_of_simplyConnected_cover
    c.projection c.isCoveringMap x ⟨q, hq⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.smoothCylinderCover.finite_fundamentalGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.smoothCylinderCover.finite_fundamentalGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.smoothCylinderCover.finite_fundamentalGroup ``Submission.DifferentialGeometry.Topology.smoothCylinderCover.finite_fundamentalGroup

theorem exists_euclidean_open_cover (c : smoothCylinderCover M) :
    ∃ p : DifferentialGeometry.Topology.Manifold.puncturedSpace (EuclideanSpace ℝ (Fin 3)) → M,
      IsCoveringMap p ∧ Function.Surjective p ∧
        IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  let D := DifferentialGeometry.Topology.Manifold.sphereProdRealDiffeomorphPunctured (n := 2) sphereTwoNorth
  refine ⟨c.projection ∘ D.symm, c.isCoveringMap.comp_homeomorph D.symm.toHomeomorph,
    c.surjective.comp D.symm.surjective, ?_⟩
  intro x
  exact (D.symm.isLocalDiffeomorph x).comp (𝓡 3) M (c.isLocalDiffeomorph (D.symm x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.smoothCylinderCover.exists_euclidean_open_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.smoothCylinderCover.exists_euclidean_open_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.smoothCylinderCover.exists_euclidean_open_cover ``Submission.DifferentialGeometry.Topology.smoothCylinderCover.exists_euclidean_open_cover

end smoothCylinderCover
end DifferentialGeometry.Topology
