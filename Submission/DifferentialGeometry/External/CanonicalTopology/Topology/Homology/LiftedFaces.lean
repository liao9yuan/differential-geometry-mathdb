import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.LiftedSimplex
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CarrierMaps

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # The same original face maps on lifted simplex bodies -/

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicTopology _root_.ContinuousMap _root_.Set _root_.Module

universe u

namespace DifferentialGeometry.Topology

/-- The original barycentric coordinate pushforward as a continuous linear
map on the lifted finite coordinate spaces. -/
def liftedSimplexLinearMap (n m : ℕ) (f : Fin (n + 1) → Fin (m + 1)) :
    liftedSimplexSpace.{u} n →L[ℝ] liftedSimplexSpace.{u} m :=
  (ContinuousLinearEquiv.ulift : liftedSimplexSpace.{u} m ≃L[ℝ] (Fin (m + 1) → ℝ)).symm.toContinuousLinearMap ∘L
    (⟨FunOnFinite.linearMap ℝ ℝ f, FunOnFinite.continuous_linearMap ℝ ℝ f⟩ :
      (Fin (n + 1) → ℝ) →L[ℝ] (Fin (m + 1) → ℝ)) ∘L
        (ContinuousLinearEquiv.ulift : liftedSimplexSpace.{u} n ≃L[ℝ] (Fin (n + 1) → ℝ)).toContinuousLinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSimplexLinearMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSimplexLinearMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSimplexLinearMap ``Submission.DifferentialGeometry.Topology.liftedSimplexLinearMap

/-- Its original vertex action is exactly the specified vertex map. -/
theorem liftedSimplexLinearMap_vertex (n m : ℕ) (f : Fin (n + 1) → Fin (m + 1)) (i : Fin (n + 1)) :
    liftedSimplexLinearMap.{u} n m f (liftedSimplexVertex n i) = liftedSimplexVertex m (f i) :=
  congrArg (fun t : stdSimplex ℝ (Fin (m + 1)) => ULift.up.{u} t.val)
    (stdSimplex.map_vertex f i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSimplexLinearMap_vertex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSimplexLinearMap_vertex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSimplexLinearMap_vertex ``Submission.DifferentialGeometry.Topology.liftedSimplexLinearMap_vertex

/-- This same map preserves the actual simplex bodies. -/
theorem liftedSimplexLinearMap_body (n m : ℕ) (f : Fin (n + 1) → Fin (m + 1)) :
    MapsTo (liftedSimplexLinearMap.{u} n m f) (liftedSimplexBody n) (liftedSimplexBody m) := by
  intro x hx
  exact stdSimplex.image_linearMap f ⟨x.down, hx, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSimplexLinearMap_body then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSimplexLinearMap_body"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSimplexLinearMap_body ``Submission.DifferentialGeometry.Topology.liftedSimplexLinearMap_body

/-- Restriction of the original coordinate map to the original simplex bodies. -/
def liftedSimplexBodyMap (n m : ℕ) (f : Fin (n + 1) → Fin (m + 1)) :
    C(liftedSimplexBody.{u} n, liftedSimplexBody.{u} m) :=
  singularPairRestriction ⟨liftedSimplexLinearMap n m f, (liftedSimplexLinearMap n m f).continuous⟩
    (liftedSimplexLinearMap_body n m f)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSimplexBodyMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSimplexBodyMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSimplexBodyMap ``Submission.DifferentialGeometry.Topology.liftedSimplexBodyMap

/-- Under the exact original homeomorphisms, the body map is the original
barycentric simplex map, including every boundary face. -/
theorem liftedSimplexBodyMap_apply (n m : ℕ) (f : Fin (n + 1) → Fin (m + 1))
    (t : stdSimplex ℝ (Fin (n + 1))) :
    liftedSimplexBodyMap.{u} n m f (liftedSimplexHomeomorph.{u} n t) =
      liftedSimplexHomeomorph.{u} m (stdSimplex.map f t) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSimplexBodyMap_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSimplexBodyMap_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSimplexBodyMap_apply ``Submission.DifferentialGeometry.Topology.liftedSimplexBodyMap_apply

end DifferentialGeometry.Topology
