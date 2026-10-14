import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Analysis.Convex.Contractible

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.Metric _root_.Set _root_.Module _root_.ContinuousMap
open scoped _root_.Topology _root_.RealInnerProductSpace _root_.unitInterval
noncomputable section
namespace DifferentialGeometry.LocalDegree

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]


def poleComplement (v : _root_.Metric.sphere (0 : E) 1) : TopologicalSpace.Opens (_root_.Metric.sphere (0 : E) 1) :=
  ⟨{v}ᶜ, isOpen_compl_singleton⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.poleComplement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.poleComplement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.poleComplement ``Submission.DifferentialGeometry.LocalDegree.poleComplement

private theorem pole_ne_neg (v : _root_.Metric.sphere (0 : E) 1) : v ≠ -v := by
  intro heq
  have hh := congrArg (fun x : _root_.Metric.sphere (0 : E) 1 ↦ ⟪(v : E), (x : E)⟫) heq
  change ⟪(v : E), (v : E)⟫ = ⟪(v : E), -(v : E)⟫ at hh
  have hi : ⟪(v : E), (v : E)⟫ = 1 := by simp [norm_eq_of_mem_sphere v]
  rw [inner_neg_right, hi] at hh
  norm_num at hh

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.pole_ne_neg
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.pole_ne_neg target :: scope.openDecls } }


theorem poleComplement_sup (v : _root_.Metric.sphere (0 : E) 1) :
    poleComplement v ⊔ poleComplement (-v) = ⊤ := by
  ext x
  change (x ∈ ({v}ᶜ ∪ {-v}ᶜ : Set (_root_.Metric.sphere (0 : E) 1))) ↔ True
  simp only [_root_.Set.mem_union, _root_.Set.mem_compl_iff, _root_.Set.mem_singleton_iff, iff_true]
  by_cases h : x = v
  · exact Or.inr (h ▸ pole_ne_neg v)
  · exact Or.inl h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.poleComplement_sup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.poleComplement_sup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.poleComplement_sup ``Submission.DifferentialGeometry.LocalDegree.poleComplement_sup


def puncturedSphereHomeomorph (v : _root_.Metric.sphere (0 : E) 1) :
    poleComplement v ≃ₜ (ℝ ∙ (v : E))ᗮ :=
  (stereographic (norm_eq_of_mem_sphere v)).toHomeomorphSourceTarget.trans
    (Homeomorph.Set.univ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.puncturedSphereHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.puncturedSphereHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.puncturedSphereHomeomorph ``Submission.DifferentialGeometry.LocalDegree.puncturedSphereHomeomorph


theorem puncturedSphereHomeomorph_apply (v : _root_.Metric.sphere (0 : E) 1) (x : poleComplement v) :
    puncturedSphereHomeomorph v x =
      (2 / (1 - ⟪(v : E), (x.val : E)⟫)) • (ℝ ∙ (v : E))ᗮ.orthogonalProjectionOnto x.val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.puncturedSphereHomeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.puncturedSphereHomeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.puncturedSphereHomeomorph_apply ``Submission.DifferentialGeometry.LocalDegree.puncturedSphereHomeomorph_apply


theorem contractibleSpace_poleComplement (v : _root_.Metric.sphere (0 : E) 1) :
    ContractibleSpace (poleComplement v) :=
  (puncturedSphereHomeomorph v).contractibleSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.contractibleSpace_poleComplement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.contractibleSpace_poleComplement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.contractibleSpace_poleComplement ``Submission.DifferentialGeometry.LocalDegree.contractibleSpace_poleComplement

private theorem stereographic_eq_zero_iff (v x : _root_.Metric.sphere (0 : E) 1)
    (hx : x ≠ v) : stereographic (norm_eq_of_mem_sphere v) x = 0 ↔ x = -v := by
  constructor
  · intro hz
    apply (stereographic (norm_eq_of_mem_sphere v)).injOn hx
      (Ne.symm (pole_ne_neg v))
    exact hz.trans (stereographic_apply_neg v).symm
  · intro h
    rw [h]
    exact stereographic_apply_neg v

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.stereographic_eq_zero_iff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.stereographic_eq_zero_iff target :: scope.openDecls } }


def poleIntersection (v : _root_.Metric.sphere (0 : E) 1) : TopologicalSpace.Opens (_root_.Metric.sphere (0 : E) 1) :=
  poleComplement v ⊓ poleComplement (-v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.poleIntersection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.poleIntersection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.poleIntersection ``Submission.DifferentialGeometry.LocalDegree.poleIntersection


abbrev EquatorialSphere (v : _root_.Metric.sphere (0 : E) 1) :=
  _root_.Metric.sphere (0 : (ℝ ∙ (v : E))ᗮ) 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.EquatorialSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.EquatorialSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.EquatorialSphere ``Submission.DifferentialGeometry.LocalDegree.EquatorialSphere

private def intersectionAsSubtype (v : _root_.Metric.sphere (0 : E) 1) :
    poleIntersection v ≃ₜ {x : poleComplement v // x.val ≠ -v} where
  toFun x := ⟨⟨x.val, x.property.1⟩, x.property.2⟩
  invFun x := ⟨x.val.val, ⟨x.val.property, x.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.intersectionAsSubtype
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.intersectionAsSubtype target :: scope.openDecls } }

def poleIntersectionPuncturedHomeomorph (v : _root_.Metric.sphere (0 : E) 1) :
    poleIntersection v ≃ₜ ({0}ᶜ : Set (ℝ ∙ (v : E))ᗮ) :=
  (intersectionAsSubtype v).trans
    ((puncturedSphereHomeomorph v).subtype (fun x ↦
      (not_congr (stereographic_eq_zero_iff v x.val x.property)).symm))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.poleIntersectionPuncturedHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.poleIntersectionPuncturedHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.poleIntersectionPuncturedHomeomorph ``Submission.DifferentialGeometry.LocalDegree.poleIntersectionPuncturedHomeomorph

def poleIntersectionHomeomorph (v : _root_.Metric.sphere (0 : E) 1) :
    poleIntersection v ≃ₜ (EquatorialSphere v × _root_.Set.Ioi (0 : ℝ)) :=
  (poleIntersectionPuncturedHomeomorph v).trans (homeomorphUnitSphereProd _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.poleIntersectionHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.poleIntersectionHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.poleIntersectionHomeomorph ``Submission.DifferentialGeometry.LocalDegree.poleIntersectionHomeomorph


theorem poleIntersectionHomeomorph_direction (v : _root_.Metric.sphere (0 : E) 1)
    (x : poleIntersection v) :
    ((poleIntersectionHomeomorph v x).1 : (ℝ ∙ (v : E))ᗮ) =
      ‖stereographic (norm_eq_of_mem_sphere v) x.val‖⁻¹ •
        stereographic (norm_eq_of_mem_sphere v) x.val :=
  homeomorphUnitSphereProd_apply_fst_coe _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.poleIntersectionHomeomorph_direction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.poleIntersectionHomeomorph_direction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.poleIntersectionHomeomorph_direction ``Submission.DifferentialGeometry.LocalDegree.poleIntersectionHomeomorph_direction


theorem poleIntersectionHomeomorph_radius (v : _root_.Metric.sphere (0 : E) 1)
    (x : poleIntersection v) :
    ((poleIntersectionHomeomorph v x).2 : ℝ) =
      ‖stereographic (norm_eq_of_mem_sphere v) x.val‖ :=
  homeomorphUnitSphereProd_apply_snd_coe _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.poleIntersectionHomeomorph_radius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.poleIntersectionHomeomorph_radius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.poleIntersectionHomeomorph_radius ``Submission.DifferentialGeometry.LocalDegree.poleIntersectionHomeomorph_radius

theorem poleIntersectionHomeomorph_symm_apply (v : _root_.Metric.sphere (0 : E) 1)
    (e : EquatorialSphere v) (r : _root_.Set.Ioi (0 : ℝ)) :
    (((poleIntersectionHomeomorph v).symm (e, r)).val : E) =
      ((r : ℝ) ^ 2 + 4)⁻¹ •
        ((4 * (r : ℝ)) • (e.val : E) + ((r : ℝ) ^ 2 - 4) • (v : E)) := by
  let w := (homeomorphUnitSphereProd (ℝ ∙ (v : E))ᗮ).symm (e, r)
  have hw : (w : (ℝ ∙ (v : E))ᗮ) = (r : ℝ) • (e : (ℝ ∙ (v : E))ᗮ) :=
    homeomorphUnitSphereProd_symm_apply_coe _ _
  have hnorm : ‖(w : (ℝ ∙ (v : E))ᗮ)‖ = (r : ℝ) := by
    rw [hw, norm_smul, Real.norm_of_nonneg r.property.le, norm_eq_of_mem_sphere e, mul_one]
  change (stereoInvFun (norm_eq_of_mem_sphere v) (w : (ℝ ∙ (v : E))ᗮ) : E) = _
  rw [stereoInvFun_apply, hnorm, hw]
  simp only [Submodule.coe_smul_of_tower, smul_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.poleIntersectionHomeomorph_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.poleIntersectionHomeomorph_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.poleIntersectionHomeomorph_symm_apply ``Submission.DifferentialGeometry.LocalDegree.poleIntersectionHomeomorph_symm_apply

private def productPositiveHomotopyEquiv (X : Type*) [TopologicalSpace X] :
    (X × _root_.Set.Ioi (0 : ℝ)) ≃ₕ X where
  toFun := ⟨Prod.fst, continuous_fst⟩
  invFun := (ContinuousMap.id X).prodMk (ContinuousMap.const X ⟨2, by norm_num⟩)
  left_inv := ⟨{
    toFun := fun p ↦ (p.2.1, ⟨(1 - (p.1 : ℝ)) * 2 + (p.1 : ℝ) * (p.2.2 : ℝ),
      (convex_Ioi (0 : ℝ)) (show (2 : ℝ) ∈ _root_.Set.Ioi (0 : ℝ) by norm_num) p.2.2.property
        (sub_nonneg.mpr p.1.property.2) p.1.property.1 (sub_add_cancel 1 (p.1 : ℝ))⟩)
    continuous_toFun := by fun_prop
    map_zero_left := by intro p; ext <;> simp
    map_one_left := by intro p; ext <;> simp }⟩
  right_inv := by
    apply ContinuousMap.Homotopic.refl

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.productPositiveHomotopyEquiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.productPositiveHomotopyEquiv target :: scope.openDecls } }

def poleIntersectionHomotopyEquiv (v : _root_.Metric.sphere (0 : E) 1) :
    poleIntersection v ≃ₕ EquatorialSphere v :=
  (poleIntersectionHomeomorph v).toHomotopyEquiv.trans (productPositiveHomotopyEquiv _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.poleIntersectionHomotopyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.poleIntersectionHomotopyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.poleIntersectionHomotopyEquiv ``Submission.DifferentialGeometry.LocalDegree.poleIntersectionHomotopyEquiv


theorem poleIntersectionHomotopyEquiv_apply (v : _root_.Metric.sphere (0 : E) 1)
    (x : poleIntersection v) :
    (poleIntersectionHomotopyEquiv v x : (ℝ ∙ (v : E))ᗮ) =
      ‖stereographic (norm_eq_of_mem_sphere v) x.val‖⁻¹ •
        stereographic (norm_eq_of_mem_sphere v) x.val :=
  poleIntersectionHomeomorph_direction v x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.poleIntersectionHomotopyEquiv_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.poleIntersectionHomotopyEquiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.poleIntersectionHomotopyEquiv_apply ``Submission.DifferentialGeometry.LocalDegree.poleIntersectionHomotopyEquiv_apply

theorem poleIntersectionHomotopyEquiv_symm_apply (v : _root_.Metric.sphere (0 : E) 1)
    (e : EquatorialSphere v) :
    (((poleIntersectionHomotopyEquiv v).symm e).val : E) = (e.val : E) := by
  have hh := poleIntersectionHomeomorph_symm_apply v e ⟨2, by norm_num⟩
  change (((poleIntersectionHomeomorph v).symm (e, ⟨2, by norm_num⟩)).val : E) = _
  rw [hh]
  norm_num [smul_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.poleIntersectionHomotopyEquiv_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.poleIntersectionHomotopyEquiv_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.poleIntersectionHomotopyEquiv_symm_apply ``Submission.DifferentialGeometry.LocalDegree.poleIntersectionHomotopyEquiv_symm_apply

def poleIntersectionRetractionHomotopy (v : _root_.Metric.sphere (0 : E) 1) :
    (ContinuousMap.id (poleIntersection v)).Homotopy
      ((poleIntersectionHomotopyEquiv v).symm.toFun.comp (poleIntersectionHomotopyEquiv v).toFun) where
  toFun p := (poleIntersectionHomeomorph v).symm
    ((poleIntersectionHomeomorph v p.2).1,
      ⟨(1 - (p.1 : ℝ)) * ((poleIntersectionHomeomorph v p.2).2 : ℝ) + (p.1 : ℝ) * 2,
        (convex_Ioi (0 : ℝ)) (poleIntersectionHomeomorph v p.2).2.property
          (show (2 : ℝ) ∈ _root_.Set.Ioi (0 : ℝ) by norm_num)
          (sub_nonneg.mpr p.1.property.2) p.1.property.1 (sub_add_cancel 1 (p.1 : ℝ))⟩)
  continuous_toFun := by fun_prop
  map_zero_left x := by
    change (poleIntersectionHomeomorph v).symm _ = x
    convert (poleIntersectionHomeomorph v).symm_apply_apply x using 1
    ext
    simp
  map_one_left x := by
    change (poleIntersectionHomeomorph v).symm _ =
      (poleIntersectionHomeomorph v).symm ((poleIntersectionHomeomorph v x).1, ⟨2, by norm_num⟩)
    congr 1
    ext <;> simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.poleIntersectionRetractionHomotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.poleIntersectionRetractionHomotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.poleIntersectionRetractionHomotopy ``Submission.DifferentialGeometry.LocalDegree.poleIntersectionRetractionHomotopy


theorem poleIntersectionRetractionHomotopy_coordinates (v : _root_.Metric.sphere (0 : E) 1)
    (t : I) (x : poleIntersection v) :
    poleIntersectionHomeomorph v (poleIntersectionRetractionHomotopy v (t, x)) =
      ((poleIntersectionHomeomorph v x).1,
        ⟨(1 - (t : ℝ)) * ((poleIntersectionHomeomorph v x).2 : ℝ) + (t : ℝ) * 2,
          (convex_Ioi (0 : ℝ)) (poleIntersectionHomeomorph v x).2.property
            (show (2 : ℝ) ∈ _root_.Set.Ioi (0 : ℝ) by norm_num)
            (sub_nonneg.mpr t.property.2) t.property.1 (sub_add_cancel 1 (t : ℝ))⟩) :=
  (poleIntersectionHomeomorph v).apply_symm_apply _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.poleIntersectionRetractionHomotopy_coordinates then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.poleIntersectionRetractionHomotopy_coordinates"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.poleIntersectionRetractionHomotopy_coordinates ``Submission.DifferentialGeometry.LocalDegree.poleIntersectionRetractionHomotopy_coordinates


theorem poleIntersectionRetractionHomotopy_fixed (v : _root_.Metric.sphere (0 : E) 1)
    (t : I) (e : EquatorialSphere v) :
    poleIntersectionRetractionHomotopy v (t, (poleIntersectionHomotopyEquiv v).symm e) =
      (poleIntersectionHomotopyEquiv v).symm e := by
  apply (poleIntersectionHomeomorph v).injective
  rw [poleIntersectionRetractionHomotopy_coordinates]
  have heq : poleIntersectionHomeomorph v ((poleIntersectionHomotopyEquiv v).symm e) =
      (e, ⟨2, by norm_num⟩) := (poleIntersectionHomeomorph v).apply_symm_apply _
  rw [heq]
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    dsimp
    ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.poleIntersectionRetractionHomotopy_fixed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.poleIntersectionRetractionHomotopy_fixed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.poleIntersectionRetractionHomotopy_fixed ``Submission.DifferentialGeometry.LocalDegree.poleIntersectionRetractionHomotopy_fixed

def equatorialSphereHomeomorph (n : ℕ) [Fact (_root_.Module.finrank ℝ E = n + 1)]
    (v : _root_.Metric.sphere (0 : E) 1) :
    EquatorialSphere v ≃ₜ _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  ((OrthonormalBasis.fromOrthogonalSpanSingleton n (ne_zero_of_mem_unit_sphere v)).repr.toHomeomorph).subtype
    (fun w ↦ by
      simp only [_root_.Metric.mem_sphere, dist_zero_right]
      change ‖w‖ = 1 ↔ ‖(OrthonormalBasis.fromOrthogonalSpanSingleton n
        (ne_zero_of_mem_unit_sphere v)).repr w‖ = 1
      rw [LinearIsometryEquiv.norm_map])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.equatorialSphereHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.equatorialSphereHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.equatorialSphereHomeomorph ``Submission.DifferentialGeometry.LocalDegree.equatorialSphereHomeomorph

theorem isEmpty_poleIntersection_of_finrank_one [Fact (_root_.Module.finrank ℝ E = 1)]
    (v : _root_.Metric.sphere (0 : E) 1) : IsEmpty (poleIntersection v) := by
  have : Fact (_root_.Module.finrank ℝ E = 0 + 1) := ⟨Fact.out⟩
  exact ⟨fun x ↦ isEmptyElim (equatorialSphereHomeomorph 0 v ((poleIntersectionHomeomorph v x).1))⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.isEmpty_poleIntersection_of_finrank_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.isEmpty_poleIntersection_of_finrank_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.isEmpty_poleIntersection_of_finrank_one ``Submission.DifferentialGeometry.LocalDegree.isEmpty_poleIntersection_of_finrank_one


def euclideanNorth (n : ℕ) : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
  ⟨EuclideanSpace.single 0 1, by simp⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanNorth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanNorth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanNorth ``Submission.DifferentialGeometry.LocalDegree.euclideanNorth


theorem euclidean_poleCover (n : ℕ) :
    poleComplement (euclideanNorth n) ⊔ poleComplement (-(euclideanNorth n)) = ⊤ :=
  poleComplement_sup _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclidean_poleCover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclidean_poleCover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclidean_poleCover ``Submission.DifferentialGeometry.LocalDegree.euclidean_poleCover

def euclideanPoleIntersectionHomotopyEquiv (n : ℕ) :
    poleIntersection (euclideanNorth n) ≃ₕ _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  letI : Fact (_root_.Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) := ⟨by simp⟩
  exact (poleIntersectionHomotopyEquiv _).trans
    (equatorialSphereHomeomorph n _).toHomotopyEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanPoleIntersectionHomotopyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanPoleIntersectionHomotopyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanPoleIntersectionHomotopyEquiv ``Submission.DifferentialGeometry.LocalDegree.euclideanPoleIntersectionHomotopyEquiv


theorem isEmpty_euclideanZeroSphereIntersection : IsEmpty (poleIntersection (euclideanNorth 0)) := by
  let : Fact (_root_.Module.finrank ℝ (EuclideanSpace ℝ (Fin (0 + 1))) = 1) := ⟨by simp⟩
  exact isEmpty_poleIntersection_of_finrank_one _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.isEmpty_euclideanZeroSphereIntersection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.isEmpty_euclideanZeroSphereIntersection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.isEmpty_euclideanZeroSphereIntersection ``Submission.DifferentialGeometry.LocalDegree.isEmpty_euclideanZeroSphereIntersection

end DifferentialGeometry.LocalDegree
