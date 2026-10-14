import Submission.DifferentialGeometry.Topology.SimplicialComplex.GeometricRealizationHomeomorphism

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.CategoryTheory _root_.Simplicial _root_.Opposite

namespace DifferentialGeometry.Topology.SimplicialComplex

universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E]
  (K : Geometry.SimplicialComplex ℝ E) (f : E → ℝ)

def vertexLabelSingularMap : orderedSimplicialSet K.toPreAbstractSimplicialComplex ⟶
    TopCat.toSSet.obj (TopCat.of (ULift.{u} ℝ)) where
  app n := ↾fun s ↦ (TopCat.toSSetObjEquiv (TopCat.of (ULift.{u} ℝ)) n).symm
    ⟨fun x ↦ ULift.up (DifferentialGeometry.Simplex.vertexMap (f ∘ s.val.obj) x),
      continuous_uliftUp.comp (DifferentialGeometry.Simplex.vertexMap (f ∘ s.val.obj)).continuous⟩
  naturality {m n} φ := by
    ext s
    apply (TopCat.toSSetObjEquiv (TopCat.of (ULift.{u} ℝ)) n).injective
    apply ContinuousMap.ext
    intro x
    apply ULift.ext
    exact (DifferentialGeometry.Simplex.vertexMap_map (f ∘ s.val.obj) φ.unop.toOrderHom x).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.vertexLabelSingularMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.vertexLabelSingularMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.vertexLabelSingularMap ``Submission.DifferentialGeometry.Topology.SimplicialComplex.vertexLabelSingularMap

def realizationVertexFunction :
    C(SSet.toTop.obj (orderedSimplicialSet K.toPreAbstractSimplicialComplex), ℝ) where
  toFun x := ((sSetTopAdj.homEquiv _ _).symm (vertexLabelSingularMap K f) x).down
  continuous_toFun := continuous_uliftDown.comp
    ((sSetTopAdj.homEquiv _ _).symm (vertexLabelSingularMap K f)).hom.continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.realizationVertexFunction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.realizationVertexFunction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.realizationVertexFunction ``Submission.DifferentialGeometry.Topology.SimplicialComplex.realizationVertexFunction


theorem realizationVertexFunction_unit_apply {n : SimplexCategoryᵒᵖ}
    (s : (orderedSimplicialSet K.toPreAbstractSimplicialComplex).obj n)
    (t : stdSimplex ℝ (Fin (n.unop.len + 1))) :
    realizationVertexFunction K f ((TopCat.toSSetObjEquiv _ n)
      ((sSetTopAdj.unit.app (orderedSimplicialSet K.toPreAbstractSimplicialComplex)).app n s) t) =
        DifferentialGeometry.Simplex.vertexMap (f ∘ s.val.obj) t := by
  have hh : sSetTopAdj.unit.app (orderedSimplicialSet K.toPreAbstractSimplicialComplex) ≫
      TopCat.toSSet.map ((sSetTopAdj.homEquiv _ _).symm (vertexLabelSingularMap K f)) =
        vertexLabelSingularMap K f :=
    (sSetTopAdj.homEquiv _ _).apply_symm_apply (vertexLabelSingularMap K f)
  exact congrArg (fun g ↦ ((TopCat.toSSetObjEquiv (TopCat.of (ULift.{u} ℝ)) n)
    (g.app n s) t).down) hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.realizationVertexFunction_unit_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.realizationVertexFunction_unit_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.realizationVertexFunction_unit_apply ``Submission.DifferentialGeometry.Topology.SimplicialComplex.realizationVertexFunction_unit_apply

def vertexFunction [Finite K.faces] : C(K.space, ℝ) :=
  (realizationVertexFunction K f).comp
    ⟨(geometricRealizationHomeomorphism K).symm,
      (geometricRealizationHomeomorphism K).symm.continuous⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.vertexFunction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.vertexFunction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.vertexFunction ``Submission.DifferentialGeometry.Topology.SimplicialComplex.vertexFunction

theorem vertexFunction_geometricSimplexMap [Finite K.faces] {n : SimplexCategoryᵒᵖ}
    (s : (orderedSimplicialSet K.toPreAbstractSimplicialComplex).obj n)
    (t : stdSimplex ℝ (Fin (n.unop.len + 1))) :
    vertexFunction K f (geometricSimplexMap K s t) =
      DifferentialGeometry.Simplex.vertexMap (f ∘ s.val.obj) t := by
  let y := (TopCat.toSSetObjEquiv _ n)
    ((sSetTopAdj.unit.app (orderedSimplicialSet K.toPreAbstractSimplicialComplex)).app n s) t
  have hg : geometricRealizationHomeomorphism K y = geometricSimplexMap K s t :=
    geometricRealizationMap_unit_apply K s t
  change realizationVertexFunction K f
    ((geometricRealizationHomeomorphism K).symm (geometricSimplexMap K s t)) = _
  rw [← hg, Homeomorph.symm_apply_apply]
  exact realizationVertexFunction_unit_apply K f s t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.vertexFunction_geometricSimplexMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.vertexFunction_geometricSimplexMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.vertexFunction_geometricSimplexMap ``Submission.DifferentialGeometry.Topology.SimplicialComplex.vertexFunction_geometricSimplexMap

theorem vertexFunction_geometricFaceHomeomorphism [Finite K.faces] {s : Finset E}
    (hs : s ∈ K.faces) (x : stdSimplex ℝ s) :
    vertexFunction K f
      ⟨(geometricFaceHomeomorphism K hs x).val,
        Geometry.SimplicialComplex.convexHull_subset_space hs
          (geometricFaceHomeomorphism K hs x).prop⟩ =
      DifferentialGeometry.Simplex.vertexMap (fun i : s ↦ f i.val) x := by
  let n := s.card - 1
  have hn : s.card = n + 1 :=
    (Nat.sub_add_cancel (Finset.card_pos.mpr (K.nonempty_of_mem_faces hs))).symm
  let e := (s.orderIsoOfFin hn).toEquiv
  let t := (DifferentialGeometry.Simplex.reindexHomeomorph e).symm x
  let a := (orderedSimplexOfFace K.toPreAbstractSimplicialComplex s hs hn).val
  have hg : geometricSimplexMap K a t =
      ⟨(geometricFaceHomeomorphism K hs x).val,
        Geometry.SimplicialComplex.convexHull_subset_space hs
          (geometricFaceHomeomorphism K hs x).prop⟩ := by
    apply Subtype.ext
    have he := DifferentialGeometry.Simplex.vertexMap_reindex e (fun i : s ↦ (i : E)) t
    rw [show DifferentialGeometry.Simplex.reindexHomeomorph e t = x from
      (DifferentialGeometry.Simplex.reindexHomeomorph e).apply_symm_apply x] at he
    exact he.symm
  rw [← hg, vertexFunction_geometricSimplexMap]
  have he := DifferentialGeometry.Simplex.vertexMap_reindex e (fun i : s ↦ f i.val) t
  rw [show DifferentialGeometry.Simplex.reindexHomeomorph e t = x from
    (DifferentialGeometry.Simplex.reindexHomeomorph e).apply_symm_apply x] at he
  exact he.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.vertexFunction_geometricFaceHomeomorphism then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.vertexFunction_geometricFaceHomeomorphism"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.vertexFunction_geometricFaceHomeomorphism ``Submission.DifferentialGeometry.Topology.SimplicialComplex.vertexFunction_geometricFaceHomeomorphism


theorem vertexFunction_vertex [Finite K.faces] {p : E} (hp : {p} ∈ K.faces)
    (x : K.space) (hx : x.val = p) : vertexFunction K f x = f p := by
  let a : stdSimplex ℝ ({p} : Finset E) :=
    stdSimplex.vertex ⟨p, Finset.mem_singleton_self p⟩
  have hd : (⟨p, Finset.mem_singleton_self p⟩ : ({p} : Finset E)) = default :=
    Subsingleton.elim _ _
  have he : (geometricFaceHomeomorphism K hp a : E) = p := by
    simp [geometricFaceHomeomorphism_apply, DifferentialGeometry.Simplex.vertexMap_apply, a,
      stdSimplex.vertex, Pi.single_apply, hd]
  have hg : (⟨(geometricFaceHomeomorphism K hp a).val,
      Geometry.SimplicialComplex.convexHull_subset_space hp
        (geometricFaceHomeomorphism K hp a).prop⟩ : K.space) = x :=
    Subtype.ext (he.trans hx.symm)
  have h := vertexFunction_geometricFaceHomeomorphism K f hp a
  rw [hg] at h
  simpa [DifferentialGeometry.Simplex.vertexMap_apply, a, stdSimplex.vertex, Pi.single_apply, hd] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.vertexFunction_vertex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.vertexFunction_vertex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.vertexFunction_vertex ``Submission.DifferentialGeometry.Topology.SimplicialComplex.vertexFunction_vertex

private theorem vertexMap_combo {ι G : Type*} [Fintype ι]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (v : ι → G)
    (x y : stdSimplex ℝ ι) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    DifferentialGeometry.Simplex.vertexMap v
      ⟨a • x.val + b • y.val, (convex_stdSimplex ℝ ι) x.prop y.prop ha hb hab⟩ =
      a • DifferentialGeometry.Simplex.vertexMap v x + b • DifferentialGeometry.Simplex.vertexMap v y := by
  simp only [DifferentialGeometry.Simplex.vertexMap_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, add_smul, _root_.SemigroupAction.mul_smul, Finset.sum_add_distrib, Finset.smul_sum]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SimplicialComplex.vertexMap_combo
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SimplicialComplex.vertexMap_combo target :: scope.openDecls } }

theorem vertexFunction_combo [Finite K.faces] {s : Finset E} (hs : s ∈ K.faces)
    (x y : K.space) (hx : x.val ∈ convexHull ℝ (s : Set E))
    (hy : y.val ∈ convexHull ℝ (s : Set E)) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    vertexFunction K f
      ⟨a • x.val + b • y.val, Geometry.SimplicialComplex.convexHull_subset_space hs
        ((convex_convexHull ℝ (s : Set E)) hx hy ha hb hab)⟩ =
      a * vertexFunction K f x + b * vertexFunction K f y := by
  let qx := (geometricFaceHomeomorphism K hs).symm ⟨x.val, hx⟩
  let qy := (geometricFaceHomeomorphism K hs).symm ⟨y.val, hy⟩
  have he (z : K.space) (hz : z.val ∈ convexHull ℝ (s : Set E)) :
      DifferentialGeometry.Simplex.vertexMap (fun i : s ↦ (i : E))
        ((geometricFaceHomeomorphism K hs).symm ⟨z.val, hz⟩) = z.val :=
    congrArg (fun z : convexHull ℝ (s : Set E) ↦ z.val)
      ((geometricFaceHomeomorphism K hs).apply_symm_apply ⟨z.val, hz⟩)
  have hf (z : K.space) (hz : z.val ∈ convexHull ℝ (s : Set E)) :
      vertexFunction K f z = DifferentialGeometry.Simplex.vertexMap (fun i : s ↦ f i.val)
        ((geometricFaceHomeomorphism K hs).symm ⟨z.val, hz⟩) := by
    have h := vertexFunction_geometricFaceHomeomorphism K f hs
      ((geometricFaceHomeomorphism K hs).symm ⟨z.val, hz⟩)
    have hz' : (⟨(geometricFaceHomeomorphism K hs
        ((geometricFaceHomeomorphism K hs).symm ⟨z.val, hz⟩)).val,
        Geometry.SimplicialComplex.convexHull_subset_space hs
          (geometricFaceHomeomorphism K hs
            ((geometricFaceHomeomorphism K hs).symm ⟨z.val, hz⟩)).prop⟩ : K.space) = z :=
      Subtype.ext (he z hz)
    rwa [hz'] at h
  let q : stdSimplex ℝ s := ⟨a • qx.val + b • qy.val,
    (convex_stdSimplex ℝ s) qx.prop qy.prop ha hb hab⟩
  have hq : (geometricFaceHomeomorphism K hs q : E) = a • x.val + b • y.val := by
    change DifferentialGeometry.Simplex.vertexMap (fun i : s ↦ (i : E)) q = _
    rw [vertexMap_combo _ qx qy ha hb hab, he, he]
  have h := vertexFunction_geometricFaceHomeomorphism K f hs q
  have hg : (⟨(geometricFaceHomeomorphism K hs q).val,
      Geometry.SimplicialComplex.convexHull_subset_space hs
        (geometricFaceHomeomorphism K hs q).prop⟩ : K.space) =
      ⟨a • x.val + b • y.val, Geometry.SimplicialComplex.convexHull_subset_space hs
        ((convex_convexHull ℝ (s : Set E)) hx hy ha hb hab)⟩ := Subtype.ext hq
  rw [hg, vertexMap_combo _ qx qy ha hb hab] at h
  simpa only [smul_eq_mul, hf x hx, hf y hy] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.vertexFunction_combo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.vertexFunction_combo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.vertexFunction_combo ``Submission.DifferentialGeometry.Topology.SimplicialComplex.vertexFunction_combo

end DifferentialGeometry.Topology.SimplicialComplex
