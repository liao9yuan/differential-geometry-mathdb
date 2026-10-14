import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.Analysis.Normed.Module.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.CategoryTheory _root_.Opposite _root_.Simplicial

universe u

namespace DifferentialGeometry.Homology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]


def affineSimplex {n : ℕ} (v : Fin (n + 1) → E) :
    C(stdSimplex ℝ (Fin (n + 1)), E) where
  toFun x := ∑ i, x i • v i
  continuous_toFun := continuous_finsetSum _ (fun i _ ↦
    ((continuous_apply i).comp continuous_subtype_val).smul continuous_const)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.affineSimplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.affineSimplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.affineSimplex ``Submission.DifferentialGeometry.Homology.affineSimplex


theorem affineSimplex_apply {n : ℕ} (v : Fin (n + 1) → E)
    (x : stdSimplex ℝ (Fin (n + 1))) : affineSimplex v x = ∑ i, x i • v i := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.affineSimplex_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.affineSimplex_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.affineSimplex_apply ``Submission.DifferentialGeometry.Homology.affineSimplex_apply


@[simp]
theorem affineSimplex_vertex {n : ℕ} (v : Fin (n + 1) → E) (i : Fin (n + 1)) :
    affineSimplex v (stdSimplex.vertex i) = v i := by
  simp [affineSimplex, Pi.single_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.affineSimplex_vertex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.affineSimplex_vertex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.affineSimplex_vertex ``Submission.DifferentialGeometry.Homology.affineSimplex_vertex

theorem affineSimplex_comp_map {n m : ℕ} (v : Fin (n + 1) → E)
    (f : Fin (m + 1) → Fin (n + 1)) :
    (affineSimplex v).comp ⟨stdSimplex.map f, stdSimplex.continuous_map f⟩ =
      affineSimplex (v ∘ f) := by
  ext x
  change ∑ j, (FunOnFinite.linearMap ℝ ℝ f x.val) j • v j = ∑ i, x i • v (f i)
  simp only [FunOnFinite.linearMap_apply_apply, Finset.sum_smul]
  calc
    _ = ∑ j, ∑ i ∈ Finset.univ with f i = j, x i • v (f i) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
      rfl
    _ = _ := Finset.sum_fiberwise Finset.univ f _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.affineSimplex_comp_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.affineSimplex_comp_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.affineSimplex_comp_map ``Submission.DifferentialGeometry.Homology.affineSimplex_comp_map


theorem range_affineSimplex_subset {n : ℕ} (v : Fin (n + 1) → E) {s : Set E}
    (hs : Convex ℝ s) (hv : ∀ i, v i ∈ s) : Set.range (affineSimplex v) ⊆ s := by
  rintro _ ⟨x, rfl⟩
  exact hs.sum_mem (fun i _ ↦ x.property.1 i) x.property.2 (fun i _ ↦ hv i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.range_affineSimplex_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.range_affineSimplex_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.range_affineSimplex_subset ``Submission.DifferentialGeometry.Homology.range_affineSimplex_subset


def affineSimplexIn {s : Set E} (hs : Convex ℝ s) {n : ℕ} (v : Fin (n + 1) → s) :
    C(stdSimplex ℝ (Fin (n + 1)), s) :=
  ⟨fun x ↦ ⟨affineSimplex (fun i ↦ (v i : E)) x,
      range_affineSimplex_subset _ hs (fun i ↦ (v i).property) ⟨x, rfl⟩⟩,
    (affineSimplex (fun i ↦ (v i : E))).continuous.subtype_mk _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.affineSimplexIn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.affineSimplexIn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.affineSimplexIn ``Submission.DifferentialGeometry.Homology.affineSimplexIn


def affineSingularSimplex {n : ℕ} (v : Fin (n + 1) → E) :
    TopCat.toSSet.obj (TopCat.of E) _⦋n⦌ :=
  ((TopCat.of E).toSSetObjEquiv (_root_.Opposite.op ⦋n⦌)).symm (affineSimplex v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.affineSingularSimplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.affineSingularSimplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.affineSingularSimplex ``Submission.DifferentialGeometry.Homology.affineSingularSimplex


def singularSimplexVertices {n : ℕ} (σ : TopCat.toSSet.obj (TopCat.of E) _⦋n⦌) :
    Fin (n + 1) → E :=
  fun i ↦ (TopCat.of E).toSSetObjEquiv (_root_.Opposite.op ⦋n⦌) σ (stdSimplex.vertex i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.singularSimplexVertices then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.singularSimplexVertices"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.singularSimplexVertices ``Submission.DifferentialGeometry.Homology.singularSimplexVertices


@[simp]
theorem singularSimplexVertices_affineSingularSimplex {n : ℕ} (v : Fin (n + 1) → E) :
    singularSimplexVertices (affineSingularSimplex v) = v := by
  funext i
  exact affineSimplex_vertex v i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.singularSimplexVertices_affineSingularSimplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.singularSimplexVertices_affineSingularSimplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.singularSimplexVertices_affineSingularSimplex ``Submission.DifferentialGeometry.Homology.singularSimplexVertices_affineSingularSimplex

omit [NormedSpace ℝ E] in
theorem singularSimplexVertices_map {n m : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : TopCat.toSSet.obj (TopCat.of E) _⦋n⦌) :
    singularSimplexVertices ((TopCat.toSSet.obj (TopCat.of E)).map f.op σ) =
      singularSimplexVertices σ ∘ f := by
  funext i
  change (TopCat.of E).toSSetObjEquiv (_root_.Opposite.op ⦋n⦌) σ
      (stdSimplex.map f (stdSimplex.vertex i)) = _
  rw [stdSimplex.map_vertex]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.singularSimplexVertices_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.singularSimplexVertices_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.singularSimplexVertices_map ``Submission.DifferentialGeometry.Homology.singularSimplexVertices_map

omit [NormedSpace ℝ E] in
@[simp]
theorem singularSimplexVertices_δ {n : ℕ}
    (σ : TopCat.toSSet.obj (TopCat.of E) _⦋n + 1⦌) (i : Fin (n + 2)) :
    singularSimplexVertices ((TopCat.toSSet.obj (TopCat.of E)).δ i σ) =
      singularSimplexVertices σ ∘ i.succAbove :=
  singularSimplexVertices_map (SimplexCategory.δ i) σ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.singularSimplexVertices_δ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.singularSimplexVertices_δ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.singularSimplexVertices_δ ``Submission.DifferentialGeometry.Homology.singularSimplexVertices_δ


theorem map_affineSingularSimplex {n m : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) (v : Fin (n + 1) → E) :
    (TopCat.toSSet.obj (TopCat.of E)).map f.op (affineSingularSimplex v) =
      affineSingularSimplex (v ∘ f) := by
  apply ((TopCat.of E).toSSetObjEquiv (_root_.Opposite.op ⦋m⦌)).injective
  change (affineSimplex v).comp
    ⟨stdSimplex.map f, stdSimplex.continuous_map f⟩ = affineSimplex (v ∘ f)
  exact affineSimplex_comp_map v f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.map_affineSingularSimplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.map_affineSingularSimplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.map_affineSingularSimplex ``Submission.DifferentialGeometry.Homology.map_affineSingularSimplex

def affineStraightening : TopCat.toSSet.obj (TopCat.of E) ⟶ TopCat.toSSet.obj (TopCat.of E) where
  app n := ↾fun σ ↦ affineSingularSimplex (n := n.unop.len) (singularSimplexVertices σ)
  naturality n m f := by
    ext σ
    change affineSingularSimplex (singularSimplexVertices
      ((TopCat.toSSet.obj (TopCat.of E)).map f σ)) =
        (TopCat.toSSet.obj (TopCat.of E)).map f
          (affineSingularSimplex (singularSimplexVertices σ))
    exact (congrArg affineSingularSimplex (singularSimplexVertices_map f.unop σ)).trans
      (map_affineSingularSimplex f.unop (singularSimplexVertices σ)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.affineStraightening then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.affineStraightening"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.affineStraightening ``Submission.DifferentialGeometry.Homology.affineStraightening


@[simp]
theorem affineStraightening_affineSingularSimplex {n : ℕ} (v : Fin (n + 1) → E) :
    (affineStraightening (E := E)).app (_root_.Opposite.op ⦋n⦌) (affineSingularSimplex v) =
      affineSingularSimplex v := by
  change affineSingularSimplex (singularSimplexVertices (affineSingularSimplex v)) = _
  rw [singularSimplexVertices_affineSingularSimplex]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.affineStraightening_affineSingularSimplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.affineStraightening_affineSingularSimplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.affineStraightening_affineSingularSimplex ``Submission.DifferentialGeometry.Homology.affineStraightening_affineSingularSimplex


theorem affineSingularSimplex_vertices_zero (σ : TopCat.toSSet.obj (TopCat.of E) _⦋0⦌) :
    affineSingularSimplex (singularSimplexVertices σ) = σ := by
  apply ((TopCat.of E).toSSetObjEquiv (_root_.Opposite.op ⦋0⦌)).injective
  ext x
  obtain rfl := Subsingleton.elim x (stdSimplex.vertex (0 : Fin 1))
  exact affineSimplex_vertex _ 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.affineSingularSimplex_vertices_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.affineSingularSimplex_vertices_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.affineSingularSimplex_vertices_zero ``Submission.DifferentialGeometry.Homology.affineSingularSimplex_vertices_zero


@[simp]
theorem δ_affineSingularSimplex {n : ℕ} (v : Fin (n + 2) → E) (i : Fin (n + 2)) :
    (TopCat.toSSet.obj (TopCat.of E)).δ i (affineSingularSimplex v) =
      affineSingularSimplex (v ∘ i.succAbove) := by
  apply ((TopCat.of E).toSSetObjEquiv (_root_.Opposite.op ⦋n⦌)).injective
  change (affineSimplex v).comp
    ⟨stdSimplex.map i.succAbove, stdSimplex.continuous_map i.succAbove⟩ =
      affineSimplex (v ∘ i.succAbove)
  exact affineSimplex_comp_map v i.succAbove

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.δ_affineSingularSimplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.δ_affineSingularSimplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.δ_affineSingularSimplex ``Submission.DifferentialGeometry.Homology.δ_affineSingularSimplex


def affineSingularSimplexIn {s : Set E} (hs : Convex ℝ s) {n : ℕ}
    (v : Fin (n + 1) → s) : TopCat.toSSet.obj (TopCat.of s) _⦋n⦌ :=
  ((TopCat.of s).toSSetObjEquiv (_root_.Opposite.op ⦋n⦌)).symm (affineSimplexIn hs v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.affineSingularSimplexIn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.affineSingularSimplexIn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.affineSingularSimplexIn ``Submission.DifferentialGeometry.Homology.affineSingularSimplexIn


theorem affineSingularSimplexIn_inclusion {s : Set E} (hs : Convex ℝ s) {n : ℕ}
    (v : Fin (n + 1) → s) :
    (TopCat.toSSet.map (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(s, E)))).app
      (_root_.Opposite.op ⦋n⦌) (affineSingularSimplexIn hs v) =
        affineSingularSimplex (fun i ↦ (v i : E)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.affineSingularSimplexIn_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.affineSingularSimplexIn_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.affineSingularSimplexIn_inclusion ``Submission.DifferentialGeometry.Homology.affineSingularSimplexIn_inclusion

end DifferentialGeometry.Homology
