import Submission.DifferentialGeometry.Topology.LocalDegree.Product.Geometry
import Submission.DifferentialGeometry.Topology.LocalDegree.SphereSuspension
import Submission.DifferentialGeometry.Topology.LocalDegree.AffineCoordinate

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.Metric _root_.Set
noncomputable section
namespace DifferentialGeometry.LocalDegree


abbrev EuclideanProductEquator (d : ℕ) := (ℝ ∙ (euclideanNorth (d + 1)).val)ᗮ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.EuclideanProductEquator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.EuclideanProductEquator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.EuclideanProductEquator ``Submission.DifferentialGeometry.LocalDegree.EuclideanProductEquator


def euclideanProductCoordinates (d : ℕ) :
    EuclideanProductEquator d ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (d + 1)) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((d + 1) + 1))) = (d + 1) + 1) := ⟨by simp⟩
  exact (OrthonormalBasis.fromOrthogonalSpanSingleton (d + 1)
    (ne_zero_of_mem_unit_sphere (euclideanNorth (d + 1)))).repr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanProductCoordinates then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanProductCoordinates"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanProductCoordinates ``Submission.DifferentialGeometry.LocalDegree.euclideanProductCoordinates


@[simp]
theorem euclideanProductCoordinates_sphere (d : ℕ)
    (v : _root_.Metric.sphere (0 : EuclideanProductEquator d) 1) :
    (euclideanSuspensionEquatorHomeomorph d v).val = euclideanProductCoordinates d v.val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanProductCoordinates_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanProductCoordinates_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanProductCoordinates_sphere ``Submission.DifferentialGeometry.LocalDegree.euclideanProductCoordinates_sphere


@[simp]
theorem euclideanProductCoordinates_symm_sphere (d : ℕ) (v : EuclideanSphere d) :
    ((euclideanSuspensionEquatorHomeomorph d).symm v).val =
      (euclideanProductCoordinates d).symm v.val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanProductCoordinates_symm_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanProductCoordinates_symm_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanProductCoordinates_symm_sphere ``Submission.DifferentialGeometry.LocalDegree.euclideanProductCoordinates_symm_sphere


def euclideanEquatorialField {d : ℕ}
    (F : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)))
    (x : EuclideanProductEquator d) : EuclideanProductEquator d :=
  (euclideanProductCoordinates d).symm (F (euclideanProductCoordinates d x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanEquatorialField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanEquatorialField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanEquatorialField ``Submission.DifferentialGeometry.LocalDegree.euclideanEquatorialField


def euclideanProductField {d : ℕ}
    (F : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))) :
    EuclideanSpace ℝ (Fin ((d + 1) + 1)) → EuclideanSpace ℝ (Fin ((d + 1) + 1)) :=
  orthogonalProductField (EuclideanProductEquator d) (euclideanEquatorialField F)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanProductField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanProductField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanProductField ``Submission.DifferentialGeometry.LocalDegree.euclideanProductField


def euclideanProductPoint (d : ℕ) (v : EuclideanSpace ℝ (Fin (d + 1))) (t : ℝ) :
    EuclideanSpace ℝ (Fin ((d + 1) + 1)) :=
  ((euclideanProductCoordinates d).symm v : EuclideanSpace ℝ (Fin ((d + 1) + 1))) +
    t • (euclideanNorth (d + 1)).val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanProductPoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanProductPoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanProductPoint ``Submission.DifferentialGeometry.LocalDegree.euclideanProductPoint


@[simp]
theorem euclideanProductPoint_projection (d : ℕ) (v : EuclideanSpace ℝ (Fin (d + 1))) (t : ℝ) :
    (EuclideanProductEquator d).orthogonalProjectionOnto (euclideanProductPoint d v t) =
      (euclideanProductCoordinates d).symm v := by
  simp [euclideanProductPoint, map_add, map_smul,
    Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanProductPoint_projection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanProductPoint_projection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanProductPoint_projection ``Submission.DifferentialGeometry.LocalDegree.euclideanProductPoint_projection


theorem euclideanProductPoint_orthogonalProjection (d : ℕ)
    (v : EuclideanSpace ℝ (Fin (d + 1))) (t : ℝ) :
    (EuclideanProductEquator d)ᗮ.starProjection (euclideanProductPoint d v t) =
      t • (euclideanNorth (d + 1)).val := by
  rw [Submodule.starProjection_orthogonal_val]
  change euclideanProductPoint d v t -
    ((EuclideanProductEquator d).orthogonalProjectionOnto (euclideanProductPoint d v t) :
      EuclideanSpace ℝ (Fin ((d + 1) + 1))) = _
  rw [euclideanProductPoint_projection]
  exact add_sub_cancel_left _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanProductPoint_orthogonalProjection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanProductPoint_orthogonalProjection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanProductPoint_orthogonalProjection ``Submission.DifferentialGeometry.LocalDegree.euclideanProductPoint_orthogonalProjection


@[simp]
theorem euclideanProductField_point {d : ℕ}
    (F : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)))
    (v : EuclideanSpace ℝ (Fin (d + 1))) (t : ℝ) :
    euclideanProductField F (euclideanProductPoint d v t) = euclideanProductPoint d (F v) t := by
  change ((euclideanProductCoordinates d).symm
    (F (euclideanProductCoordinates d
      ((EuclideanProductEquator d).orthogonalProjectionOnto (euclideanProductPoint d v t)))) :
        EuclideanSpace ℝ (Fin ((d + 1) + 1))) +
    (EuclideanProductEquator d)ᗮ.starProjection (euclideanProductPoint d v t) = _
  rw [euclideanProductPoint_projection, LinearIsometryEquiv.apply_symm_apply,
    euclideanProductPoint_orthogonalProjection]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanProductField_point then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanProductField_point"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanProductField_point ``Submission.DifferentialGeometry.LocalDegree.euclideanProductField_point


@[simp]
theorem euclideanProductPoint_height (d : ℕ) (v : EuclideanSpace ℝ (Fin (d + 1))) (t : ℝ) :
    inner ℝ (euclideanNorth (d + 1)).val (euclideanProductPoint d v t) = t := by
  have hi := Submodule.mem_orthogonal_singleton_iff_inner_right.mp
    ((euclideanProductCoordinates d).symm v).property
  change _root_.Inner.inner ℝ (euclideanNorth (d + 1)).val
    (((euclideanProductCoordinates d).symm v : EuclideanSpace ℝ (Fin ((d + 1) + 1))) +
      t • (euclideanNorth (d + 1)).val) = t
  rw [inner_add_right, hi, inner_smul_right]
  simp [norm_eq_of_mem_sphere]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanProductPoint_height then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanProductPoint_height"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanProductPoint_height ``Submission.DifferentialGeometry.LocalDegree.euclideanProductPoint_height


theorem euclideanProduct_orthogonalProjection (d : ℕ)
    (y : EuclideanSpace ℝ (Fin ((d + 1) + 1))) :
    (EuclideanProductEquator d)ᗮ.starProjection y =
      inner ℝ (euclideanNorth (d + 1)).val y • (euclideanNorth (d + 1)).val := by
  change (ℝ ∙ (euclideanNorth (d + 1)).val)ᗮᗮ.starProjection y = _
  simp only [Submodule.orthogonal_orthogonal,
    Submodule.starProjection_unit_singleton ℝ (norm_eq_of_mem_sphere (euclideanNorth (d + 1)))]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanProduct_orthogonalProjection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanProduct_orthogonalProjection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanProduct_orthogonalProjection ``Submission.DifferentialGeometry.LocalDegree.euclideanProduct_orthogonalProjection


theorem euclideanProductPoint_reconstruct (d : ℕ)
    (y : EuclideanSpace ℝ (Fin ((d + 1) + 1))) :
    euclideanProductPoint d
      (euclideanProductCoordinates d ((EuclideanProductEquator d).orthogonalProjectionOnto y))
      (_root_.Inner.inner ℝ (euclideanNorth (d + 1)).val y) = y := by
  unfold euclideanProductPoint
  rw [LinearIsometryEquiv.symm_apply_apply, ← euclideanProduct_orthogonalProjection]
  exact (EuclideanProductEquator d).starProjection_add_starProjection_orthogonal y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanProductPoint_reconstruct then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanProductPoint_reconstruct"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanProductPoint_reconstruct ``Submission.DifferentialGeometry.LocalDegree.euclideanProductPoint_reconstruct


def euclideanProductChart (d : ℕ) :
    EuclideanSpace ℝ (Fin ((d + 1) + 1)) ≃L[ℝ] (EuclideanSpace ℝ (Fin (d + 1)) × ℝ) :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun := fun y ↦ (euclideanProductCoordinates d
      ((EuclideanProductEquator d).orthogonalProjectionOnto y),
      _root_.Inner.inner ℝ (euclideanNorth (d + 1)).val y)
    invFun := fun p ↦ euclideanProductPoint d p.1 p.2
    left_inv := euclideanProductPoint_reconstruct d
    right_inv := by intro p; ext <;> simp
    map_add' := by intro x y; ext <;> simp [map_add, inner_add_right]
    map_smul' := by intro c x; ext <;> simp [map_smul, inner_smul_right] }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanProductChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanProductChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanProductChart ``Submission.DifferentialGeometry.LocalDegree.euclideanProductChart


@[simp]
theorem euclideanProductChart_symm_apply (d : ℕ) (p : EuclideanSpace ℝ (Fin (d + 1)) × ℝ) :
    (euclideanProductChart d).symm p = euclideanProductPoint d p.1 p.2 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanProductChart_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanProductChart_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanProductChart_symm_apply ``Submission.DifferentialGeometry.LocalDegree.euclideanProductChart_symm_apply


theorem euclideanProductChart_field {d : ℕ}
    (F : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)))
    (p : EuclideanSpace ℝ (Fin (d + 1)) × ℝ) :
    euclideanProductChart d (euclideanProductField F ((euclideanProductChart d).symm p)) =
      (F p.1, p.2) := by
  rw [euclideanProductChart_symm_apply, euclideanProductField_point]
  exact (euclideanProductChart d).apply_symm_apply (F p.1, p.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanProductChart_field then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanProductChart_field"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanProductChart_field ``Submission.DifferentialGeometry.LocalDegree.euclideanProductChart_field


theorem IsolatingRadius.euclideanEquator {d : ℕ}
    {F : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {R : ℝ} (h : IsolatingRadius F 0 R) :
    IsolatingRadius (euclideanEquatorialField F) 0 R := by
  have hm : _root_.Set.MapsTo (euclideanProductCoordinates d)
      (_root_.Metric.closedBall (0 : EuclideanProductEquator d) R)
      (_root_.Metric.closedBall (0 : EuclideanSpace ℝ (Fin (d + 1))) R) := by
    intro x hx
    simpa only [_root_.Metric.mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map] using hx
  refine ⟨h.pos, ?_, ?_⟩
  · exact (euclideanProductCoordinates d).symm.continuous.comp_continuousOn
      (h.continuousOn.comp (euclideanProductCoordinates d).continuous.continuousOn hm)
  · intro x hx
    change (euclideanProductCoordinates d).symm (F (euclideanProductCoordinates d x)) = 0 ↔ x = 0
    rw [(euclideanProductCoordinates d).symm.map_eq_zero_iff, h.zero_iff _ (hm hx),
      (euclideanProductCoordinates d).map_eq_zero_iff]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.IsolatingRadius.euclideanEquator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.IsolatingRadius.euclideanEquator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.IsolatingRadius.euclideanEquator ``Submission.DifferentialGeometry.LocalDegree.IsolatingRadius.euclideanEquator


theorem IsolatingRadius.euclideanProduct {d : ℕ}
    {F : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {R : ℝ} (h : IsolatingRadius F 0 R) :
    IsolatingRadius (euclideanProductField F) 0 R :=
  h.euclideanEquator.orthogonalProduct (EuclideanProductEquator d)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.IsolatingRadius.euclideanProduct then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.IsolatingRadius.euclideanProduct"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.IsolatingRadius.euclideanProduct ``Submission.DifferentialGeometry.LocalDegree.IsolatingRadius.euclideanProduct


theorem isolatedZero_euclideanProduct {d : ℕ}
    {F : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    (h : isolatedZero F 0) : isolatedZero (euclideanProductField F) 0 :=
  ⟨h.choose, h.choose_spec.euclideanProduct⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.isolatedZero_euclideanProduct then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.isolatedZero_euclideanProduct"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.isolatedZero_euclideanProduct ``Submission.DifferentialGeometry.LocalDegree.isolatedZero_euclideanProduct


theorem sphereMap_euclideanEquatorialField {d : ℕ}
    {F : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {R : ℝ} (h : IsolatingRadius F 0 R) (r : _root_.Set.Ioc (0 : ℝ) R) :
    sphereMap (euclideanEquatorialField F) 0 R h.euclideanEquator.continuousOn
        h.euclideanEquator.nonzero r =
      euclideanSuspensionEquatorMap (sphereMap F 0 R h.continuousOn h.nonzero r) := by
  apply ContinuousMap.ext
  intro v
  apply Subtype.ext
  rw [sphereMap_apply]
  change ‖(euclideanProductCoordinates d).symm
      (F (euclideanProductCoordinates d (0 + (r : ℝ) • v.val)))‖⁻¹ •
      (euclideanProductCoordinates d).symm
        (F (euclideanProductCoordinates d (0 + (r : ℝ) • v.val))) =
    (euclideanProductCoordinates d).symm
      (sphereMap F 0 R h.continuousOn h.nonzero r (euclideanSuspensionEquatorHomeomorph d v)).val
  rw [sphereMap_apply, zero_add, zero_add, map_smul,
    LinearIsometryEquiv.norm_map, euclideanProductCoordinates_sphere, map_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.sphereMap_euclideanEquatorialField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.sphereMap_euclideanEquatorialField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.sphereMap_euclideanEquatorialField ``Submission.DifferentialGeometry.LocalDegree.sphereMap_euclideanEquatorialField


def euclideanProductSphereHomotopy {d : ℕ}
    {F : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {R : ℝ} (h : IsolatingRadius F 0 R) (r : _root_.Set.Ioc (0 : ℝ) R) :
    (sphereMap (euclideanProductField F) 0 R h.euclideanProduct.continuousOn
        h.euclideanProduct.nonzero r).Homotopy
      (euclideanSphereSuspension (sphereMap F 0 R h.continuousOn h.nonzero r)) :=
  (orthogonalProductSphereHomotopy (EuclideanProductEquator d) h.euclideanEquator r).cast
    rfl (by rw [sphereMap_euclideanEquatorialField h r]; rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanProductSphereHomotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanProductSphereHomotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanProductSphereHomotopy ``Submission.DifferentialGeometry.LocalDegree.euclideanProductSphereHomotopy


theorem euclideanLocalDegree_product_zero {d : ℕ}
    {F : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    (h : isolatedZero F 0) :
    euclideanLocalDegree (euclideanProductField F) 0 (isolatedZero_euclideanProduct h) =
      euclideanLocalDegree F 0 h := by
  have hR := h.choose_spec
  let r : _root_.Set.Ioc (0 : ℝ) h.choose := ⟨h.choose, hR.pos, le_rfl⟩
  rw [euclideanLocalDegree_eq_sphereDegree _ hR.euclideanProduct r,
    euclideanLocalDegree_eq_sphereDegree h hR r,
    euclideanSphereDegree_eq_of_homotopy (euclideanProductSphereHomotopy hR r),
    euclideanSphereDegree_suspension]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanLocalDegree_product_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanLocalDegree_product_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanLocalDegree_product_zero ``Submission.DifferentialGeometry.LocalDegree.euclideanLocalDegree_product_zero


theorem euclideanProductField_translate {d : ℕ}
    (F : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)))
    (x : EuclideanSpace ℝ (Fin (d + 1))) (y : EuclideanSpace ℝ (Fin ((d + 1) + 1))) :
    euclideanProductField F (euclideanProductPoint d x 0 + y) =
      euclideanProductField (fun v ↦ F (x + v)) y := by
  change ((euclideanProductCoordinates d).symm
    (F (euclideanProductCoordinates d ((EuclideanProductEquator d).orthogonalProjectionOnto
      (euclideanProductPoint d x 0 + y)))) : EuclideanSpace ℝ (Fin ((d + 1) + 1))) +
    (EuclideanProductEquator d)ᗮ.starProjection (euclideanProductPoint d x 0 + y) = _
  rw [map_add, euclideanProductPoint_projection, map_add,
    LinearIsometryEquiv.apply_symm_apply, map_add, euclideanProductPoint_orthogonalProjection,
    zero_smul, zero_add]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanProductField_translate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanProductField_translate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanProductField_translate ``Submission.DifferentialGeometry.LocalDegree.euclideanProductField_translate

private theorem isolatedZero_translate {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {F : D → D} {x : D} (h : isolatedZero F x) : isolatedZero (fun y ↦ F (x + y)) 0 := by
  simpa using isolatedZero_affineCoordinate (ContinuousLinearEquiv.refl ℝ D) 0 x h

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.isolatedZero_translate
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.isolatedZero_translate target :: scope.openDecls } }

private theorem localDegree_translate {d : ℕ}
    {F : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {x : EuclideanSpace ℝ (Fin (d + 1))} (h : isolatedZero F x) :
    euclideanLocalDegree (fun y ↦ F (x + y)) 0 (isolatedZero_translate h) =
      euclideanLocalDegree F x h := by
  simpa using euclideanLocalDegree_affineCoordinate
    (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin (d + 1)))) 0 x h

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.localDegree_translate
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.localDegree_translate target :: scope.openDecls } }


theorem isolatedZero_euclideanProduct_at {d : ℕ}
    {F : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {x : EuclideanSpace ℝ (Fin (d + 1))} (h : isolatedZero F x) :
    isolatedZero (euclideanProductField F) (euclideanProductPoint d x 0) := by
  have hshift := isolatedZero_euclideanProduct (isolatedZero_translate h)
  have hh := isolatedZero_affineCoordinate
    (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin ((d + 1) + 1))))
    (euclideanProductPoint d x 0) 0 hshift
  have heq : (fun y ↦ euclideanProductField (fun v ↦ F (x + v))
      (y - euclideanProductPoint d x 0)) = euclideanProductField F := by
    funext y
    rw [← euclideanProductField_translate, add_sub_cancel]
  simpa only [ContinuousLinearEquiv.refl_apply, ContinuousLinearEquiv.refl_symm, zero_add, heq] using hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.isolatedZero_euclideanProduct_at then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.isolatedZero_euclideanProduct_at"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.isolatedZero_euclideanProduct_at ``Submission.DifferentialGeometry.LocalDegree.isolatedZero_euclideanProduct_at


theorem euclideanLocalDegree_product {d : ℕ}
    {F : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {x : EuclideanSpace ℝ (Fin (d + 1))} (h : isolatedZero F x) :
    euclideanLocalDegree (euclideanProductField F) (euclideanProductPoint d x 0)
        (isolatedZero_euclideanProduct_at h) = euclideanLocalDegree F x h := by
  have heq : (fun y ↦ euclideanProductField F (euclideanProductPoint d x 0 + y)) =
      euclideanProductField (fun v ↦ F (x + v)) :=
    funext (euclideanProductField_translate F x)
  have hp := localDegree_translate (isolatedZero_euclideanProduct_at h)
  have hp' : euclideanLocalDegree (euclideanProductField (fun v ↦ F (x + v))) 0
      (isolatedZero_euclideanProduct (isolatedZero_translate h)) =
    euclideanLocalDegree (euclideanProductField F) (euclideanProductPoint d x 0)
      (isolatedZero_euclideanProduct_at h) := by
    simpa only [heq] using hp
  rw [← hp', euclideanLocalDegree_product_zero (isolatedZero_translate h), localDegree_translate h]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanLocalDegree_product then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanLocalDegree_product"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanLocalDegree_product ``Submission.DifferentialGeometry.LocalDegree.euclideanLocalDegree_product

end DifferentialGeometry.LocalDegree
