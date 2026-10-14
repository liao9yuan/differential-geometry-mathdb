import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CochainMaps
import Mathlib.CategoryTheory.Linear.Yoneda
import Mathlib.Algebra.Homology.Opposite
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Topology.Homotopy.Equiv

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicTopology

universe u

namespace DifferentialGeometry.Topology

def integralSingularCochainsDualIso (X : Type u) [TopologicalSpace X] :
    (((_root_.CategoryTheory.linearYoneda ℤ (ModuleCat.{u} ℤ)).obj integralSingularCoefficients).mapHomologicalComplex
      (.up ℕ)).obj (integralSingularChains X).op ≅ integralSingularCochains X := by
  refine HomologicalComplex.Hom.isoOfComponents (fun n =>
    (ModuleCat.homLinearEquiv (R := ℤ) (S := ℤ)
      (M := (integralSingularChains X).X n)
      (N := integralSingularCoefficients)).toModuleIso) ?_
  intro i j _
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro c
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCochainsDualIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCochainsDualIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCochainsDualIso ``Submission.DifferentialGeometry.Topology.integralSingularCochainsDualIso

theorem integralSingularCochainsDualIso_natural
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : ContinuousMap X Y) :
    (integralSingularCochainsDualIso Y).hom ≫ integralSingularCochainMap f =
      (((_root_.CategoryTheory.linearYoneda ℤ (ModuleCat.{u} ℤ)).obj integralSingularCoefficients).mapHomologicalComplex
        (.up ℕ)).map ((HomologicalComplex.opFunctor (ModuleCat.{u} ℤ) (.down ℕ)).map
          (integralSingularChainMap f).op) ≫ (integralSingularCochainsDualIso X).hom := by
  ext n : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro c
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCochainsDualIso_natural then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCochainsDualIso_natural"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCochainsDualIso_natural ``Submission.DifferentialGeometry.Topology.integralSingularCochainsDualIso_natural

def integralSingularCochainMapHomotopy
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : ContinuousMap X Y} (H : f.Homotopy g) :
    _root_.Homotopy (integralSingularCochainMap f) (integralSingularCochainMap g) := by
  let F := (_root_.CategoryTheory.linearYoneda ℤ (ModuleCat.{u} ℤ)).obj integralSingularCoefficients
  let G := HomologicalComplex.opFunctor (ModuleCat.{u} ℤ) (.down ℕ)
  let h := TopCat.Homotopy.singularChainComplexFunctorObjMap
    (show TopCat.Homotopy (TopCat.ofHom f) (TopCat.ofHom g) from H) integralSingularCoefficients
  have he (a : ContinuousMap X Y) :
      ((integralSingularCochainsDualIso Y).inv ≫
        (F.mapHomologicalComplex (ComplexShape.down ℕ).symm).map
          (G.map (integralSingularChainMap a).op)) ≫
          (integralSingularCochainsDualIso X).hom = integralSingularCochainMap a := by
    ext n : 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro c
    rfl
  exact (Homotopy.ofEq (he f).symm).trans
    (((F.mapHomotopy h.op).compLeft (integralSingularCochainsDualIso Y).inv).compRight
      (integralSingularCochainsDualIso X).hom |>.trans (Homotopy.ofEq (he g)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCochainMapHomotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCochainMapHomotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCochainMapHomotopy ``Submission.DifferentialGeometry.Topology.integralSingularCochainMapHomotopy

theorem integralSingularCohomologyMap_eq_of_homotopic
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : ContinuousMap X Y} (h : f.Homotopic g) (n : ℕ) :
    integralSingularCohomologyMap n f = integralSingularCohomologyMap n g := by
  obtain ⟨H⟩ := h
  exact congrArg (fun a => a.hom) ((integralSingularCochainMapHomotopy H).homologyMap_eq n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCohomologyMap_eq_of_homotopic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCohomologyMap_eq_of_homotopic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCohomologyMap_eq_of_homotopic ``Submission.DifferentialGeometry.Topology.integralSingularCohomologyMap_eq_of_homotopic

theorem integralSingularCohomologyMap_bijective_of_homotopyEquiv
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    Function.Bijective (integralSingularCohomologyMap n ⟨e, e.continuous⟩) := by
  have hleft : Function.LeftInverse
      (integralSingularCohomologyMap n ⟨e.symm, e.symm.continuous⟩)
      (integralSingularCohomologyMap n ⟨e, e.continuous⟩) := by
    have h := integralSingularCohomologyMap_eq_of_homotopic e.right_inv n
    rw [integralSingularCohomologyMap_comp, integralSingularCohomologyMap_id] at h
    exact fun α => LinearMap.congr_fun h α
  have hright : Function.RightInverse
      (integralSingularCohomologyMap n ⟨e.symm, e.symm.continuous⟩)
      (integralSingularCohomologyMap n ⟨e, e.continuous⟩) := by
    have h := integralSingularCohomologyMap_eq_of_homotopic e.left_inv n
    rw [integralSingularCohomologyMap_comp, integralSingularCohomologyMap_id] at h
    exact fun α => LinearMap.congr_fun h α
  exact ⟨hleft.injective, hright.surjective⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCohomologyMap_bijective_of_homotopyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCohomologyMap_bijective_of_homotopyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCohomologyMap_bijective_of_homotopyEquiv ``Submission.DifferentialGeometry.Topology.integralSingularCohomologyMap_bijective_of_homotopyEquiv

end DifferentialGeometry.Topology

end
