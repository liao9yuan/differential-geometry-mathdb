import Submission.DifferentialGeometry.Topology.LocalDegree.SphereSuspension.Geometry
import Submission.DifferentialGeometry.Topology.LocalDegree.SphereDegree
import Submission.DifferentialGeometry.Topology.Homology.Reduced.MayerVietorisNaturality

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Metric _root_.Set
noncomputable section
universe u
namespace DifferentialGeometry.LocalDegree
open _root_.Submission.DifferentialGeometry.Homology
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]


theorem equatorSphereSuspension_maps_first (v : _root_.Metric.sphere (0 : E) 1)
    (f : C(EquatorialSphere v, EquatorialSphere v)) :
    _root_.Set.MapsTo (equatorSphereSuspension v f) (poleComplement v : Set (_root_.Metric.sphere (0 : E) 1))
      (poleComplement v : Set (_root_.Metric.sphere (0 : E) 1)) := by
  intro x hx
  exact mt (equatorSphereSuspension_eq_north_iff v f x).mp hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.equatorSphereSuspension_maps_first then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.equatorSphereSuspension_maps_first"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.equatorSphereSuspension_maps_first ``Submission.DifferentialGeometry.LocalDegree.equatorSphereSuspension_maps_first


theorem equatorSphereSuspension_maps_second (v : _root_.Metric.sphere (0 : E) 1)
    (f : C(EquatorialSphere v, EquatorialSphere v)) :
    _root_.Set.MapsTo (equatorSphereSuspension v f) (poleComplement (-v) : Set (_root_.Metric.sphere (0 : E) 1))
      (poleComplement (-v) : Set (_root_.Metric.sphere (0 : E) 1)) := by
  intro x hx
  exact mt (equatorSphereSuspension_eq_south_iff v f x).mp hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.equatorSphereSuspension_maps_second then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.equatorSphereSuspension_maps_second"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.equatorSphereSuspension_maps_second ``Submission.DifferentialGeometry.LocalDegree.equatorSphereSuspension_maps_second


def poleOverlapSuspension (v : _root_.Metric.sphere (0 : E) 1)
    (f : C(EquatorialSphere v, EquatorialSphere v)) :
    TopCat.of (poleIntersection v) ⟶ TopCat.of (poleIntersection v) :=
  relativeSubspaceMap (TopCat.ofHom (equatorSphereSuspension v f))
    ((equatorSphereSuspension_maps_first v f).inter_inter
      (equatorSphereSuspension_maps_second v f))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.poleOverlapSuspension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.poleOverlapSuspension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.poleOverlapSuspension ``Submission.DifferentialGeometry.LocalDegree.poleOverlapSuspension


theorem poleIntersectionHomotopyEquiv_inv_suspension (v : _root_.Metric.sphere (0 : E) 1)
    (f : C(EquatorialSphere v, EquatorialSphere v)) :
    TopCat.ofHom (poleIntersectionHomotopyEquiv v).invFun ≫ poleOverlapSuspension v f =
      TopCat.ofHom f ≫ TopCat.ofHom (poleIntersectionHomotopyEquiv v).invFun := by
  ext x
  change orthogonalRadialExtension (ℝ ∙ (v : E))ᗮ f
    (((poleIntersectionHomotopyEquiv v).symm x).val : E) =
      (((poleIntersectionHomotopyEquiv v).symm (f x)).val : E)
  rw [poleIntersectionHomotopyEquiv_symm_apply, poleIntersectionHomotopyEquiv_symm_apply,
    orthogonalRadialExtension_sphere]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.poleIntersectionHomotopyEquiv_inv_suspension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.poleIntersectionHomotopyEquiv_inv_suspension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.poleIntersectionHomotopyEquiv_inv_suspension ``Submission.DifferentialGeometry.LocalDegree.poleIntersectionHomotopyEquiv_inv_suspension

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)


theorem poleIntersectionHomologyIso_suspension (v : _root_.Metric.sphere (0 : E) 1)
    (f : C(EquatorialSphere v, EquatorialSphere v)) (n : ℕ) :
    reducedSingularHomologyMap R (poleOverlapSuspension v f) n ≫
      (reducedSingularHomologyIso R (poleIntersectionHomotopyEquiv v) n).hom =
    (reducedSingularHomologyIso R (poleIntersectionHomotopyEquiv v) n).hom ≫
      reducedSingularHomologyMap R (TopCat.ofHom f) n := by
  let e : reducedSingularHomology R (TopCat.of (poleIntersection v)) n ≅
      reducedSingularHomology R (TopCat.of (EquatorialSphere v)) n :=
    reducedSingularHomologyIso R (poleIntersectionHomotopyEquiv v) n
  have hh := congrArg (fun g ↦ reducedSingularHomologyMap R g n)
    (poleIntersectionHomotopyEquiv_inv_suspension v f)
  simp only [reducedSingularHomologyMap_comp] at hh
  change e.inv ≫ reducedSingularHomologyMap R (poleOverlapSuspension v f) n =
    reducedSingularHomologyMap R (TopCat.ofHom f) n ≫ e.inv at hh
  apply (_root_.CategoryTheory.cancel_epi e.inv).mp
  change e.inv ≫ (_ ≫ e.hom) = e.inv ≫ (e.hom ≫ _)
  rw [← Category.assoc, hh, Category.assoc, e.inv_hom_id, Category.comp_id,
    ← Category.assoc, e.inv_hom_id, Category.id_comp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.poleIntersectionHomologyIso_suspension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.poleIntersectionHomologyIso_suspension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.poleIntersectionHomologyIso_suspension ``Submission.DifferentialGeometry.LocalDegree.poleIntersectionHomologyIso_suspension

private theorem poleCover (v : _root_.Metric.sphere (0 : E) 1) : ∀ x : _root_.Metric.sphere (0 : E) 1,
    x ∈ (poleComplement v : Set (_root_.Metric.sphere (0 : E) 1)) ∨
      x ∈ (poleComplement (-v) : Set (_root_.Metric.sphere (0 : E) 1)) := by
  intro x
  have h : x ∈ (poleComplement v ⊔ poleComplement (-v)) := by
    rw [poleComplement_sup]
    trivial
  exact h

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.poleCover
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.poleCover target :: scope.openDecls } }

theorem sphereEquatorReducedHomologyIso_suspension (v : _root_.Metric.sphere (0 : E) 1)
    (f : C(EquatorialSphere v, EquatorialSphere v)) (n : ℕ) :
    reducedSingularHomologyMap R (TopCat.ofHom (equatorSphereSuspension v f)) (n + 1) ≫
      (sphereEquatorReducedHomologyIso R v n).hom =
    (sphereEquatorReducedHomologyIso R v n).hom ≫
      reducedSingularHomologyMap R (TopCat.ofHom f) n := by
  have hs := contractibleSpace_poleComplement v
  have ht := contractibleSpace_poleComplement (-v)
  have h := reducedMayerVietorisConnectingMap_naturality R
    (TopCat.ofHom (equatorSphereSuspension v f))
    (equatorSphereSuspension_maps_first v f) (equatorSphereSuspension_maps_second v f)
    (poleComplement v).isOpen (poleComplement (-v)).isOpen (poleCover v)
    (poleComplement v).isOpen (poleComplement (-v)).isOpen (poleCover v) n
  rw [reducedMayerVietorisConnectingMap_eq_iso] at h
  change _ ≫ (_ ≫ _) = (_ ≫ _) ≫ _
  rw [← Category.assoc, h, Category.assoc]
  have hh := poleIntersectionHomologyIso_suspension R v f n
  have hhh := congrArg (fun g ↦
    (reducedMayerVietorisConnectingIso R (TopCat.of (_root_.Metric.sphere (0 : E) 1))
      (poleComplement v : Set (_root_.Metric.sphere (0 : E) 1))
      (poleComplement (-v) : Set (_root_.Metric.sphere (0 : E) 1))
      (poleComplement v).isOpen (poleComplement (-v)).isOpen (poleCover v) n).hom ≫ g) hh
  simpa only [Category.assoc] using! hhh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.sphereEquatorReducedHomologyIso_suspension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.sphereEquatorReducedHomologyIso_suspension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.sphereEquatorReducedHomologyIso_suspension ``Submission.DifferentialGeometry.LocalDegree.sphereEquatorReducedHomologyIso_suspension


def euclideanSuspensionEquatorHomeomorph (d : ℕ) :
    EquatorialSphere (euclideanNorth (d + 1)) ≃ₜ EuclideanSphere d := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((d + 1) + 1))) = (d + 1) + 1) := ⟨by simp⟩
  exact equatorialSphereHomeomorph (d + 1) (euclideanNorth (d + 1))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanSuspensionEquatorHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanSuspensionEquatorHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanSuspensionEquatorHomeomorph ``Submission.DifferentialGeometry.LocalDegree.euclideanSuspensionEquatorHomeomorph


def euclideanSuspensionEquatorMap {d : ℕ} (f : C(EuclideanSphere d, EuclideanSphere d)) :
    C(EquatorialSphere (euclideanNorth (d + 1)), EquatorialSphere (euclideanNorth (d + 1))) :=
  (euclideanSuspensionEquatorHomeomorph d).symm.toHomotopyEquiv.toFun.comp
    (f.comp (euclideanSuspensionEquatorHomeomorph d).toHomotopyEquiv.toFun)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanSuspensionEquatorMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanSuspensionEquatorMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanSuspensionEquatorMap ``Submission.DifferentialGeometry.LocalDegree.euclideanSuspensionEquatorMap

def euclideanSphereSuspension {d : ℕ} (f : C(EuclideanSphere d, EuclideanSphere d)) :
    C(EuclideanSphere (d + 1), EuclideanSphere (d + 1)) :=
  equatorSphereSuspension (euclideanNorth (d + 1)) (euclideanSuspensionEquatorMap f)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanSphereSuspension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanSphereSuspension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanSphereSuspension ``Submission.DifferentialGeometry.LocalDegree.euclideanSphereSuspension


def euclideanSphereEquatorInclusion (d : ℕ) :
    C(EuclideanSphere d, EuclideanSphere (d + 1)) where
  toFun x := ((poleIntersectionHomotopyEquiv (euclideanNorth (d + 1))).invFun
    ((euclideanSuspensionEquatorHomeomorph d).symm x)).val
  continuous_toFun := continuous_subtype_val.comp
    ((poleIntersectionHomotopyEquiv (euclideanNorth (d + 1))).invFun.continuous.comp
      (euclideanSuspensionEquatorHomeomorph d).symm.continuous)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanSphereEquatorInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanSphereEquatorInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanSphereEquatorInclusion ``Submission.DifferentialGeometry.LocalDegree.euclideanSphereEquatorInclusion


theorem euclideanSphereSuspension_equator {d : ℕ} (f : C(EuclideanSphere d, EuclideanSphere d)) :
    (euclideanSphereSuspension f).comp (euclideanSphereEquatorInclusion d) =
      (euclideanSphereEquatorInclusion d).comp f := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change orthogonalRadialExtension (ℝ ∙ (euclideanNorth (d + 1)).val)ᗮ
      (euclideanSuspensionEquatorMap f)
      (((poleIntersectionHomotopyEquiv (euclideanNorth (d + 1))).symm
        ((euclideanSuspensionEquatorHomeomorph d).symm x)).val : EuclideanSpace ℝ (Fin ((d + 1) + 1))) =
    (((poleIntersectionHomotopyEquiv (euclideanNorth (d + 1))).symm
      ((euclideanSuspensionEquatorHomeomorph d).symm (f x))).val : EuclideanSpace ℝ (Fin ((d + 1) + 1)))
  rw [poleIntersectionHomotopyEquiv_symm_apply, poleIntersectionHomotopyEquiv_symm_apply,
    orthogonalRadialExtension_sphere]
  change (((euclideanSuspensionEquatorHomeomorph d).symm
    (f ((euclideanSuspensionEquatorHomeomorph d)
      ((euclideanSuspensionEquatorHomeomorph d).symm x)))).val : EuclideanSpace ℝ (Fin ((d + 1) + 1))) = _
  rw [Homeomorph.apply_symm_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanSphereSuspension_equator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanSphereSuspension_equator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanSphereSuspension_equator ``Submission.DifferentialGeometry.LocalDegree.euclideanSphereSuspension_equator


@[simp]
theorem euclideanSphereSuspension_north {d : ℕ} (f : C(EuclideanSphere d, EuclideanSphere d)) :
    euclideanSphereSuspension f (euclideanNorth (d + 1)) = euclideanNorth (d + 1) :=
  (equatorSphereSuspension_eq_north_iff _ _ _).mpr rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanSphereSuspension_north then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanSphereSuspension_north"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanSphereSuspension_north ``Submission.DifferentialGeometry.LocalDegree.euclideanSphereSuspension_north


@[simp]
theorem euclideanSphereSuspension_south {d : ℕ} (f : C(EuclideanSphere d, EuclideanSphere d)) :
    euclideanSphereSuspension f (-euclideanNorth (d + 1)) = -euclideanNorth (d + 1) :=
  (equatorSphereSuspension_eq_south_iff _ _ _).mpr rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanSphereSuspension_south then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanSphereSuspension_south"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanSphereSuspension_south ``Submission.DifferentialGeometry.LocalDegree.euclideanSphereSuspension_south


theorem euclideanSphereSuspension_height {d : ℕ} (f : C(EuclideanSphere d, EuclideanSphere d))
    (x : EuclideanSphere (d + 1)) :
    _root_.Inner.inner ℝ (euclideanNorth (d + 1)).val (euclideanSphereSuspension f x).val =
      inner ℝ (euclideanNorth (d + 1)).val x.val :=
  equatorSphereSuspension_height _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanSphereSuspension_height then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanSphereSuspension_height"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanSphereSuspension_height ``Submission.DifferentialGeometry.LocalDegree.euclideanSphereSuspension_height


theorem euclideanSuspensionEquatorMap_naturality {d : ℕ}
    (f : C(EuclideanSphere d, EuclideanSphere d)) :
    TopCat.ofHom (euclideanSuspensionEquatorMap f) ≫
        TopCat.ofHom (euclideanSuspensionEquatorHomeomorph d).toHomotopyEquiv.toFun =
      TopCat.ofHom (euclideanSuspensionEquatorHomeomorph d).toHomotopyEquiv.toFun ≫
        TopCat.ofHom f := by
  ext x : 1
  exact (euclideanSuspensionEquatorHomeomorph d).apply_symm_apply _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanSuspensionEquatorMap_naturality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanSuspensionEquatorMap_naturality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanSuspensionEquatorMap_naturality ``Submission.DifferentialGeometry.LocalDegree.euclideanSuspensionEquatorMap_naturality

theorem euclideanSphereReducedHomologySuccIso_suspension {k : Type} [Ring k] (R : ModuleCat k)
    {d : ℕ} (f : C(EuclideanSphere d, EuclideanSphere d)) (n : ℕ) :
    reducedSingularHomologyMap R (TopCat.ofHom (euclideanSphereSuspension f)) (n + 1) ≫
      (euclideanSphereReducedHomologySuccIso R (d + 1) n).hom =
    (euclideanSphereReducedHomologySuccIso R (d + 1) n).hom ≫
      reducedSingularHomologyMap R (TopCat.ofHom f) n := by
  have hh := congrArg (fun g ↦ reducedSingularHomologyMap R g n)
    (euclideanSuspensionEquatorMap_naturality f)
  simp only [reducedSingularHomologyMap_comp] at hh
  change reducedSingularHomologyMap R
      (TopCat.ofHom (equatorSphereSuspension (euclideanNorth (d + 1))
        (euclideanSuspensionEquatorMap f))) (n + 1) ≫ (_ ≫ _) = (_ ≫ _) ≫ _
  rw [← Category.assoc, sphereEquatorReducedHomologyIso_suspension, Category.assoc]
  have hhh := congrArg (fun g ↦
    (sphereEquatorReducedHomologyIso R (euclideanNorth (d + 1)) n).hom ≫ g) hh
  simpa only [Category.assoc] using! hhh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanSphereReducedHomologySuccIso_suspension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanSphereReducedHomologySuccIso_suspension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanSphereReducedHomologySuccIso_suspension ``Submission.DifferentialGeometry.LocalDegree.euclideanSphereReducedHomologySuccIso_suspension


theorem euclideanSphereDegree_suspension {d : ℕ} (f : C(EuclideanSphere d, EuclideanSphere d)) :
    euclideanSphereDegree (euclideanSphereSuspension f) = euclideanSphereDegree f := by
  change euclideanSphereTopReducedHomologyEquiv (d + 1) _ = _
  rw [euclideanSphereTopReducedHomologyEquiv_succ]
  change euclideanSphereTopReducedHomologyEquiv d
    ((reducedSingularHomologyMap (ModuleCat.of ℤ ℤ)
      (TopCat.ofHom (euclideanSphereSuspension f)) (d + 1) ≫
      (euclideanSphereReducedHomologySuccIso (ModuleCat.of ℤ ℤ) (d + 1) d).hom)
        (euclideanSphereTopGenerator (d + 1))) = _
  rw [euclideanSphereReducedHomologySuccIso_suspension]
  change euclideanSphereTopReducedHomologyEquiv d
    (reducedSingularHomologyMap (ModuleCat.of ℤ ℤ) (TopCat.ofHom f) d
      ((euclideanSphereReducedHomologySuccIso (ModuleCat.of ℤ ℤ) (d + 1) d).hom
        (euclideanSphereTopGenerator (d + 1)))) = _
  rw [euclideanSphereTopGenerator_connecting]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanSphereDegree_suspension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanSphereDegree_suspension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanSphereDegree_suspension ``Submission.DifferentialGeometry.LocalDegree.euclideanSphereDegree_suspension

end DifferentialGeometry.LocalDegree
