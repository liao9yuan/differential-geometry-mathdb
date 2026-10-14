import Submission.DifferentialGeometry.Topology.SimplicialComplex.VertexStarContractible
import Submission.DifferentialGeometry.Topology.SimplicialComplex.GeometricEulerCharacteristic
import Submission.DifferentialGeometry.Topology.Homology.Local.Manifold
import Submission.DifferentialGeometry.Topology.Homotopy.ConvexProduct

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.CategoryTheory _root_.ContinuousMap _root_.Submission.DifferentialGeometry.Homology
namespace DifferentialGeometry.Topology.SimplicialComplex
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E]
  (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (p : E)


def vertexStarNeighborhoodHomeomorphism :
    ((Subtype.val : K.space → E) ⁻¹' vertexOpenStar K p) ≃ₜ vertexOpenStar K p where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.vertexStarNeighborhoodHomeomorphism then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.vertexStarNeighborhoodHomeomorphism"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.vertexStarNeighborhoodHomeomorphism ``Submission.DifferentialGeometry.Topology.SimplicialComplex.vertexStarNeighborhoodHomeomorphism

variable (hp : {p} ∈ K.faces)
include hp


def puncturedOpenStarHomeomorphism :
    ({(⟨p, vertex_mem_openStar K p hp⟩ : vertexOpenStar K p)}ᶜ : Set (vertexOpenStar K p)) ≃ₜ
      puncturedVertexOpenStar K p where
  toFun x := ⟨x.val.val, x.val.property, fun h => x.property (Subtype.ext h)⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, fun h => x.property.2 (congrArg Subtype.val h)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.puncturedOpenStarHomeomorphism then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.puncturedOpenStarHomeomorphism"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.puncturedOpenStarHomeomorphism ``Submission.DifferentialGeometry.Topology.SimplicialComplex.puncturedOpenStarHomeomorphism

private theorem neighborhood_puncture_iff
    (y : (Subtype.val : K.space → E) ⁻¹' vertexOpenStar K p) :
    y ∈ ({(⟨⟨p, Geometry.SimplicialComplex.vertices_subset_space hp⟩,
        vertex_mem_openStar K p hp⟩ :
          (Subtype.val : K.space → E) ⁻¹' vertexOpenStar K p)}ᶜ : Set _) ↔
      vertexStarNeighborhoodHomeomorphism K p y ∈
        ({(⟨p, vertex_mem_openStar K p hp⟩ : vertexOpenStar K p)}ᶜ : Set _) :=
  not_congr (vertexStarNeighborhoodHomeomorphism K p).injective.eq_iff.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SimplicialComplex.neighborhood_puncture_iff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SimplicialComplex.neighborhood_puncture_iff target :: scope.openDecls } }


def puncturedVertexStarHomotopyEquiv :
    puncturedVertexOpenStar K p ≃ₕ (geometricLink K {p}).space :=
  (puncturedVertexStarHomeomorphism K p hp).toHomotopyEquiv.trans
    (DifferentialGeometry.HomotopyEquiv.productConvex _ (convex_Ioo (0 : ℝ) 1)
      ⟨1 / 2, by constructor <;> norm_num⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.puncturedVertexStarHomotopyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.puncturedVertexStarHomotopyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.puncturedVertexStarHomotopyEquiv ``Submission.DifferentialGeometry.Topology.SimplicialComplex.puncturedVertexStarHomotopyEquiv


@[simp]
theorem puncturedVertexStarHomotopyEquiv_symm_apply (y : (geometricLink K {p}).space) :
    ((puncturedVertexStarHomotopyEquiv K p hp).symm y).val =
      (1 / 2 : ℝ) • p + (1 / 2 : ℝ) • y.val := by
  change (1 / 2 : ℝ) • p + (1 - 1 / 2 : ℝ) • y.val = _
  norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.puncturedVertexStarHomotopyEquiv_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.puncturedVertexStarHomotopyEquiv_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.puncturedVertexStarHomotopyEquiv_symm_apply ``Submission.DifferentialGeometry.Topology.SimplicialComplex.puncturedVertexStarHomotopyEquiv_symm_apply


theorem finiteHomologyType_puncturedVertexStar (k : Type u) [Field k] :
    finiteHomologyType k (TopCat.of (puncturedVertexOpenStar K p)) :=
  (finiteHomologyType_iff_of_homotopyEquiv k
    (X := TopCat.of (puncturedVertexOpenStar K p))
    (Y := TopCat.of (geometricLink K {p}).space)
    (puncturedVertexStarHomotopyEquiv K p hp)).mpr
      (finiteHomologyType_geometricSpace (geometricLink K {p}) k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.finiteHomologyType_puncturedVertexStar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.finiteHomologyType_puncturedVertexStar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.finiteHomologyType_puncturedVertexStar ``Submission.DifferentialGeometry.Topology.SimplicialComplex.finiteHomologyType_puncturedVertexStar


theorem eulerChar_puncturedVertexStar (k : Type u) [Field k] :
    eulerChar k (TopCat.of (puncturedVertexOpenStar K p)) =
      eulerChar k (TopCat.of (geometricLink K {p}).space) :=
  eulerChar_eq_of_homotopyEquiv k
    (X := TopCat.of (puncturedVertexOpenStar K p))
    (Y := TopCat.of (geometricLink K {p}).space)
    (puncturedVertexStarHomotopyEquiv K p hp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.eulerChar_puncturedVertexStar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.eulerChar_puncturedVertexStar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.eulerChar_puncturedVertexStar ``Submission.DifferentialGeometry.Topology.SimplicialComplex.eulerChar_puncturedVertexStar


theorem finiteHomologyType_localGeometricVertex (k : Type u) [Field k] :
    DifferentialGeometry.HomologicalComplex.finiteHomologyType
      (relativeChainComplex (TopCat.of K.space)
        ({(⟨p, Geometry.SimplicialComplex.vertices_subset_space hp⟩ : K.space)}ᶜ : Set K.space)
        (ModuleCat.of k k)) := by
  let U : Set K.space := (Subtype.val : K.space → E) ⁻¹' vertexOpenStar K p
  let x : K.space := ⟨p, Geometry.SimplicialComplex.vertices_subset_space hp⟩
  have hx : x ∈ U := vertex_mem_openStar K p hp
  have hf := (finiteHomologyType_iff_of_homeomorph k
    (X := TopCat.of ({(⟨p, vertex_mem_openStar K p hp⟩ : vertexOpenStar K p)}ᶜ : Set _))
    (Y := TopCat.of (puncturedVertexOpenStar K p))
    (puncturedOpenStarHomeomorphism K p hp)).mpr
      (finiteHomologyType_puncturedVertexStar K p hp k)
  have hs := finiteHomologyType_relativeChainComplex (TopCat.of (vertexOpenStar K p))
    ({(⟨p, vertex_mem_openStar K p hp⟩ : vertexOpenStar K p)}ᶜ : Set _) k hf
    (finiteHomologyType_vertexOpenStar K p hp k)
  let e := relativeChainIso (X := TopCat.of U) (Y := TopCat.of (vertexOpenStar K p))
    (ModuleCat.of k k) (vertexStarNeighborhoodHomeomorphism K p)
    (neighborhood_puncture_iff K p hp)
  have hn := (DifferentialGeometry.HomologicalComplex.finiteHomologyType_iff_of_quasiIso e.hom).mpr hs
  exact (finiteHomologyType_puncturedNeighborhood_iff (TopCat.of K.space) U x hx k
    (isOpen_vertexOpenStar K p)).mp hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.finiteHomologyType_localGeometricVertex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.finiteHomologyType_localGeometricVertex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.finiteHomologyType_localGeometricVertex ``Submission.DifferentialGeometry.Topology.SimplicialComplex.finiteHomologyType_localGeometricVertex


theorem relativeEulerChar_vertex_eq_one_sub_link (k : Type u) [Field k] :
    relativeEulerChar (TopCat.of K.space)
      ({(⟨p, Geometry.SimplicialComplex.vertices_subset_space hp⟩ : K.space)}ᶜ : Set K.space) k =
        1 - eulerChar k (TopCat.of (geometricLink K {p}).space) := by
  let U : Set K.space := (Subtype.val : K.space → E) ⁻¹' vertexOpenStar K p
  let x : K.space := ⟨p, Geometry.SimplicialComplex.vertices_subset_space hp⟩
  have hx : x ∈ U := vertex_mem_openStar K p hp
  have he : ∀ y : U,
      y ∈ ({(⟨x, hx⟩ : U)}ᶜ : Set U) ↔
        vertexStarNeighborhoodHomeomorphism K p y ∈
          ({(⟨p, vertex_mem_openStar K p hp⟩ : vertexOpenStar K p)}ᶜ : Set (vertexOpenStar K p)) :=
    neighborhood_puncture_iff K p hp
  have hf := (finiteHomologyType_iff_of_homeomorph k
    (X := TopCat.of ({(⟨p, vertex_mem_openStar K p hp⟩ : vertexOpenStar K p)}ᶜ : Set _))
    (Y := TopCat.of (puncturedVertexOpenStar K p))
    (puncturedOpenStarHomeomorphism K p hp)).mpr
      (finiteHomologyType_puncturedVertexStar K p hp k)
  calc
    _ = relativeEulerChar (TopCat.of U) ({(⟨x, hx⟩ : U)}ᶜ : Set U) k :=
      (relativeEulerChar_puncturedNeighborhood (TopCat.of K.space) U x hx k
        (isOpen_vertexOpenStar K p)).symm
    _ = relativeEulerChar (TopCat.of (vertexOpenStar K p))
        ({(⟨p, vertex_mem_openStar K p hp⟩ : vertexOpenStar K p)}ᶜ : Set _) k :=
      relativeEulerChar_eq_of_homeomorph (X := TopCat.of U)
        (Y := TopCat.of (vertexOpenStar K p)) k (vertexStarNeighborhoodHomeomorphism K p) he
    _ = 1 - eulerChar k (TopCat.of (geometricLink K {p}).space) := by
      rw [relativeEulerChar_eq_sub (TopCat.of (vertexOpenStar K p))
        ({(⟨p, vertex_mem_openStar K p hp⟩ : vertexOpenStar K p)}ᶜ : Set _) k hf (finiteHomologyType_vertexOpenStar K p hp k),
        eulerChar_vertexOpenStar K p hp k,
        eulerChar_eq_of_homeomorph k
          (X := TopCat.of ({(⟨p, vertex_mem_openStar K p hp⟩ : vertexOpenStar K p)}ᶜ : Set _))
          (Y := TopCat.of (puncturedVertexOpenStar K p)) (puncturedOpenStarHomeomorphism K p hp),
        eulerChar_puncturedVertexStar K p hp k]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.relativeEulerChar_vertex_eq_one_sub_link then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.relativeEulerChar_vertex_eq_one_sub_link"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.relativeEulerChar_vertex_eq_one_sub_link ``Submission.DifferentialGeometry.Topology.SimplicialComplex.relativeEulerChar_vertex_eq_one_sub_link


theorem faceEulerChar_vertexLink_eq_one_sub_local (k : Type u) [Field k] :
    faceEulerChar (link K.toPreAbstractSimplicialComplex {p}) =
      1 - relativeEulerChar (TopCat.of K.space)
        ({(⟨p, Geometry.SimplicialComplex.vertices_subset_space hp⟩ : K.space)}ᶜ : Set K.space) k := by
  have h := relativeEulerChar_vertex_eq_one_sub_link K p hp k
  rw [eulerChar_geometricSpace_eq_faceEulerChar] at h
  change _ = 1 - faceEulerChar (link K.toPreAbstractSimplicialComplex {p}) at h
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_vertexLink_eq_one_sub_local then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_vertexLink_eq_one_sub_local"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_vertexLink_eq_one_sub_local ``Submission.DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_vertexLink_eq_one_sub_local

end DifferentialGeometry.Topology.SimplicialComplex
