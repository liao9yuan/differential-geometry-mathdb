import Submission.DifferentialGeometry.Topology.Homotopy.CubeSphereProjection

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.ContinuousMap
open scoped _root_.Topology

namespace DifferentialGeometry.Topology

variable {K X : Type*} [TopologicalSpace K] [TopologicalSpace X]



theorem cubeSphereProjection_prod_quotient (n : ℕ) (K : Type*) [TopologicalSpace K] :
    _root_.Topology.IsQuotientMap (Prod.map (id : K → K) (cubeSphereProjection n)) := by
  have hp : IsProperMap (Prod.map (id : K → K) (cubeSphereProjection n)) :=
    isProperMap_id.prodMap (cubeSphereProjection n).continuous.isProperMap
  exact hp.isClosedMap.isQuotientMap hp.continuous
    ((_root_.Function.surjective_id : _root_.Function.Surjective (id : K → K)).prodMap (cubeSphereProjection_surjective n))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cubeSphereProjection_prod_quotient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cubeSphereProjection_prod_quotient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cubeSphereProjection_prod_quotient ``Submission.DifferentialGeometry.Topology.cubeSphereProjection_prod_quotient



def sphereFamilyDescendValue (n : ℕ)
    (F : C(K × (Fin (n + 1) → unitInterval), X)) (b : C(K, X))
    (z : K × Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) : X :=
  ((cubeInteriorSphereHomeomorph n).symm z.2).elim (b z.1) (fun u => F (z.1, u.val))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereFamilyDescendValue then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereFamilyDescendValue"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereFamilyDescendValue ``Submission.DifferentialGeometry.Topology.sphereFamilyDescendValue


theorem sphereFamilyDescendValue_projection (n : ℕ)
    (F : C(K × (Fin (n + 1) → unitInterval), X)) (b : C(K, X))
    (hb : ∀ k v, v ∈ Cube.boundary (Fin (n + 1)) → F (k, v) = b k)
    (k : K) (v : Fin (n + 1) → unitInterval) :
    sphereFamilyDescendValue n F b (k, cubeSphereProjection n v) = F (k, v) := by
  classical
  change ((cubeInteriorSphereHomeomorph n).symm
    (cubeInteriorSphereHomeomorph n (openCollapse (cubeInterior _) v))).elim _ _ = _
  rw [Homeomorph.symm_apply_apply]
  by_cases hv : v ∈ cubeInterior (Fin (n + 1))
  · simp only [openCollapse, dif_pos hv, OnePoint.elim_some]
  · rw [openCollapse_of_notMem _ hv, OnePoint.elim_infty]
    exact (hb k v (by
      simpa only [cubeInterior_eq_compl_boundary, _root_.Set.mem_compl_iff, _root_.Classical.not_not] using hv)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereFamilyDescendValue_projection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereFamilyDescendValue_projection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereFamilyDescendValue_projection ``Submission.DifferentialGeometry.Topology.sphereFamilyDescendValue_projection



theorem continuous_sphereFamilyDescendValue (n : ℕ)
    (F : C(K × (Fin (n + 1) → unitInterval), X)) (b : C(K, X))
    (hb : ∀ k v, v ∈ Cube.boundary (Fin (n + 1)) → F (k, v) = b k) :
    Continuous (sphereFamilyDescendValue n F b) := by
  apply (cubeSphereProjection_prod_quotient n K).continuous_iff.mpr
  apply F.continuous.congr
  intro z
  exact (sphereFamilyDescendValue_projection n F b hb z.1 z.2).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.continuous_sphereFamilyDescendValue then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.continuous_sphereFamilyDescendValue"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.continuous_sphereFamilyDescendValue ``Submission.DifferentialGeometry.Topology.continuous_sphereFamilyDescendValue


theorem sphereFamilyDescendValue_basepoint (n : ℕ)
    (F : C(K × (Fin (n + 1) → unitInterval), X)) (b : C(K, X)) (k : K) :
    sphereFamilyDescendValue n F b (k, cubeSphereBasepoint n) = b k := by
  change ((cubeInteriorSphereHomeomorph n).symm
    (cubeInteriorSphereHomeomorph n OnePoint.infty)).elim _ _ = _
  rw [Homeomorph.symm_apply_apply, OnePoint.elim_infty]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereFamilyDescendValue_basepoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereFamilyDescendValue_basepoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereFamilyDescendValue_basepoint ``Submission.DifferentialGeometry.Topology.sphereFamilyDescendValue_basepoint

end DifferentialGeometry.Topology
