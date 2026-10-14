import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Cochains

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # Actual pullback of integral singular cochains -/

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology _root_.ContinuousMap

universe u

namespace DifferentialGeometry.Topology

variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The original singular chain functor preserves the actual identity map. -/
theorem integralSingularChainMap_id : integralSingularChainMap (.id X) = 𝟙 _ :=
  ((_root_.AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj integralSingularCoefficients).map_id
    (TopCat.of X)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularChainMap_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularChainMap_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularChainMap_id ``Submission.DifferentialGeometry.Topology.integralSingularChainMap_id

/-- Pullback evaluates each original cochain on the original image chain. -/
def integralSingularCochainPullback (n : ℕ) (f : C(X, Y)) :
    integralSingularCochain n Y →ₗ[ℤ] integralSingularCochain n X where
  toFun φ := φ.comp ((integralSingularChainMap f).f n).hom
  map_add' φ ψ := by ext c; rfl
  map_smul' k φ := by ext c; rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCochainPullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCochainPullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCochainPullback ``Submission.DifferentialGeometry.Topology.integralSingularCochainPullback

/-- Pullback is an actual morphism of the original integral cochain complexes. -/
def integralSingularCochainMap (f : C(X, Y)) :
    integralSingularCochains Y ⟶ integralSingularCochains X where
  f n := ModuleCat.ofHom (integralSingularCochainPullback n f)
  comm' i j _ := by
    apply ModuleCat.hom_ext
    change (integralSingularCoboundary X i j).comp (integralSingularCochainPullback i f) =
      (integralSingularCochainPullback j f).comp (integralSingularCoboundary Y i j)
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro c
    change φ ((integralSingularChainMap f).f i ((integralSingularChains X).d j i c)) =
      φ ((integralSingularChains Y).d j i ((integralSingularChainMap f).f j c))
    exact congrArg φ (congrArg (fun g : (integralSingularChains X).X j ⟶
      (integralSingularChains Y).X i => g c) ((integralSingularChainMap f).comm j i)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCochainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCochainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCochainMap ``Submission.DifferentialGeometry.Topology.integralSingularCochainMap

/-- The actual identity induces identity on the full cochain complex. -/
theorem integralSingularCochainMap_id : integralSingularCochainMap (.id X) = 𝟙 _ := by
  ext n : 1
  apply ModuleCat.hom_ext
  change integralSingularCochainPullback n (.id X) = LinearMap.id
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro c
  change φ ((integralSingularChainMap (.id X)).f n c) = φ c
  rw [integralSingularChainMap_id]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCochainMap_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCochainMap_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCochainMap_id ``Submission.DifferentialGeometry.Topology.integralSingularCochainMap_id

/-- Pullback reverses the original composition. -/
theorem integralSingularCochainMap_comp (f : C(X, Y)) (g : C(Y, Z)) :
    integralSingularCochainMap (g.comp f) =
      integralSingularCochainMap g ≫ integralSingularCochainMap f := by
  ext n : 1
  apply ModuleCat.hom_ext
  change integralSingularCochainPullback n (g.comp f) =
    (integralSingularCochainPullback n f).comp (integralSingularCochainPullback n g)
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro c
  change φ ((integralSingularChainMap (g.comp f)).f n c) =
    φ ((integralSingularChainMap g).f n ((integralSingularChainMap f).f n c))
  rw [integralSingularChainMap_comp]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCochainMap_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCochainMap_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCochainMap_comp ``Submission.DifferentialGeometry.Topology.integralSingularCochainMap_comp

/-- The cohomology map is induced by that same cochain pullback. -/
def integralSingularCohomologyMap (n : ℕ) (f : C(X, Y)) :
    integralSingularCohomology n Y →ₗ[ℤ] integralSingularCohomology n X :=
  (HomologicalComplex.homologyMap (integralSingularCochainMap f) n).hom

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCohomologyMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCohomologyMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCohomologyMap ``Submission.DifferentialGeometry.Topology.integralSingularCohomologyMap

/-- Identity on the original space induces identity on its cohomology. -/
theorem integralSingularCohomologyMap_id (n : ℕ) :
    integralSingularCohomologyMap n (.id X) = LinearMap.id := by
  unfold integralSingularCohomologyMap
  rw [integralSingularCochainMap_id, HomologicalComplex.homologyMap_id]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCohomologyMap_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCohomologyMap_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCohomologyMap_id ``Submission.DifferentialGeometry.Topology.integralSingularCohomologyMap_id

/-- The induced cohomology maps obey the actual contravariant composition law. -/
theorem integralSingularCohomologyMap_comp (n : ℕ) (f : C(X, Y)) (g : C(Y, Z)) :
    integralSingularCohomologyMap n (g.comp f) =
      (integralSingularCohomologyMap n f).comp (integralSingularCohomologyMap n g) := by
  unfold integralSingularCohomologyMap
  rw [integralSingularCochainMap_comp, HomologicalComplex.homologyMap_comp]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCohomologyMap_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCohomologyMap_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCohomologyMap_comp ``Submission.DifferentialGeometry.Topology.integralSingularCohomologyMap_comp

end DifferentialGeometry.Topology
