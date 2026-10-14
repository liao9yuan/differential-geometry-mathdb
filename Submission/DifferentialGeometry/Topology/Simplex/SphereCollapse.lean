import Submission.DifferentialGeometry.Topology.Simplex.Sphere
import Submission.DifferentialGeometry.Topology.Simplex.InactiveFaceContraction
import Submission.DifferentialGeometry.Topology.Simplex.VertexContraction
import Mathlib.Topology.Homotopy.Equiv

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.ContinuousMap _root_.Submission.ContinuousMap

namespace DifferentialGeometry.Simplex

variable {n : ℕ} {S : Type*} [TopologicalSpace S]

private abbrev B (n : ℕ) := boundary (Fin (n + 3))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Simplex.B
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Simplex.B target :: scope.openDecls } }

private def vertexZero (n : ℕ) : B n :=
  ⟨stdSimplex.vertex (S := ℝ) 0, ⟨1, by simp⟩⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Simplex.vertexZero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Simplex.vertexZero target :: scope.openDecls } }

private def inactive (n : ℕ) : Set (B n) :=
  {p | ∃ j : Fin (n + 3), j ≠ 0 ∧ p.val.val j = 0}

run_cmd do
  let target := ``Submission.DifferentialGeometry.Simplex.inactive
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Simplex.inactive target :: scope.openDecls } }

private def faceB (i : Fin (n + 3)) : C(stdSimplex ℝ (Fin (n + 2)), B n) where
  toFun p := ⟨stdSimplex.map i.succAbove p, ⟨i, map_succAbove_apply_pivot i p⟩⟩
  continuous_toFun := (stdSimplex.continuous_map i.succAbove).subtype_mk _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Simplex.faceB
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Simplex.faceB target :: scope.openDecls } }

private theorem face_zero_boundary (p : stdSimplex ℝ (Fin (n + 2)))
    (hp : p ∈ boundary (Fin (n + 2))) : faceB 0 p ∈ inactive n := by
  obtain ⟨j, hj⟩ := hp
  exact ⟨(0 : Fin (n + 3)).succAbove j, Fin.succAbove_ne _ _, by
    simpa only [faceB, ContinuousMap.coe_mk, map_succAbove_apply_image] using hj⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Simplex.face_zero_boundary
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Simplex.face_zero_boundary target :: scope.openDecls } }

private theorem face_inactive (i : Fin (n + 3)) (hi : i ≠ 0)
    (p : stdSimplex ℝ (Fin (n + 2))) : faceB i p ∈ inactive n :=
  ⟨i, hi, map_succAbove_apply_pivot i p⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Simplex.face_inactive
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Simplex.face_inactive target :: scope.openDecls } }

private def collapseBoundary (q : C(stdSimplex ℝ (Fin (n + 2)), S)) (b : S)
    (hb : ∀ p ∈ boundary (Fin (n + 2)), q p = b) : C(B n, S) :=
  boundaryDesc (simplexSphereFaces q b) (simplexSphereFaces_compatible q b hb)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Simplex.collapseBoundary
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Simplex.collapseBoundary target :: scope.openDecls } }

private theorem collapseBoundary_face (q : C(stdSimplex ℝ (Fin (n + 2)), S)) (b : S)
    (hb : ∀ p ∈ boundary (Fin (n + 2)), q p = b)
    (i : Fin (n + 3)) (p : stdSimplex ℝ (Fin (n + 2))) :
    collapseBoundary q b hb (faceB i p) = simplexSphereFaces q b i p :=
  boundaryDesc_face _ _ i p

run_cmd do
  let target := ``Submission.DifferentialGeometry.Simplex.collapseBoundary_face
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Simplex.collapseBoundary_face target :: scope.openDecls } }

private theorem collapseBoundary_inactive (q : C(stdSimplex ℝ (Fin (n + 2)), S)) (b : S)
    (hb : ∀ p ∈ boundary (Fin (n + 2)), q p = b)
    (p : B n) (hp : p ∈ inactive n) : collapseBoundary q b hb p = b := by
  obtain ⟨i, hi, hpi⟩ := hp
  let z := faceDelete i ⟨p.val, hpi⟩
  have he : p = faceB i z :=
    Subtype.ext (congrArg Subtype.val (faceInsert_faceDelete i ⟨p.val, hpi⟩)).symm
  rw [he, collapseBoundary_face]
  induction i using Fin.cases with
  | zero => exact (hi rfl).elim
  | succ i => rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Simplex.collapseBoundary_inactive
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Simplex.collapseBoundary_inactive target :: scope.openDecls } }

private theorem collapseBoundary_zero (q : C(stdSimplex ℝ (Fin (n + 2)), S)) (b : S)
    (hb : ∀ p ∈ boundary (Fin (n + 2)), q p = b)
    (p : stdSimplex ℝ (Fin (n + 2))) : collapseBoundary q b hb (faceB 0 p) = q p :=
  collapseBoundary_face q b hb 0 p

run_cmd do
  let target := ``Submission.DifferentialGeometry.Simplex.collapseBoundary_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Simplex.collapseBoundary_zero target :: scope.openDecls } }

private theorem exists_collapseBoundary_homotopyEquiv
    (q : C(stdSimplex ℝ (Fin (n + 2)), S)) (b : S)
    (hb : ∀ p ∈ boundary (Fin (n + 2)), q p = b)
    (hquot : _root_.Topology.IsQuotientMap q)
    (hfiber : ∀ p r, q p = q r → p = r ∨ p ∈ boundary (Fin (n + 2)) ∧ r ∈ boundary (Fin (n + 2)))
    (K : C(unitInterval × B n, B n))
    (hzero : ∀ p, K (0, p) = p)
    (hone : ∀ p ∈ inactive n, K (1, p) = vertexZero n)
    (hpres : ∀ t p, p ∈ inactive n → K (t, p) ∈ inactive n) :
    ∃ e : _root_.ContinuousMap.HomotopyEquiv (B n) S, e.toFun = collapseBoundary q b hb := by
  let g : C(stdSimplex ℝ (Fin (n + 2)), B n) :=
    K.comp ⟨fun p => (1, faceB 0 p), continuous_const.prodMk (faceB 0).continuous⟩
  have hg : ∀ p ∈ boundary (Fin (n + 2)), g p = vertexZero n :=
    fun p hp => hone (faceB 0 p) (face_zero_boundary p hp)
  have hgf : Function.FactorsThrough g q := by
    intro p r h
    obtain rfl | ⟨hp, hr⟩ := hfiber p r h
    · rfl
    · rw [hg p hp, hg r hr]
  let R := hquot.lift g hgf
  have hRg : R.comp q = g := hquot.lift_comp g hgf
  have hRb : R b = vertexZero n := by
    let v : stdSimplex ℝ (Fin (n + 2)) := stdSimplex.vertex 0
    have hv : v ∈ boundary (Fin (n + 2)) := ⟨1, by simp [v]⟩
    rw [← hb v hv]
    exact (ContinuousMap.congr_fun hRg v).trans (hg v hv)
  have hRK (p : B n) : R (collapseBoundary q b hb p) = K (1, p) := by
    obtain ⟨i, hi⟩ := p.property
    let z := faceDelete i ⟨p.val, hi⟩
    have he : p = faceB i z :=
      Subtype.ext (congrArg Subtype.val (faceInsert_faceDelete i ⟨p.val, hi⟩)).symm
    rw [he]
    by_cases hi0 : i = 0
    · subst i
      rw [collapseBoundary_zero]
      exact ContinuousMap.congr_fun hRg z
    · rw [collapseBoundary_inactive _ _ _ _ (face_inactive i hi0 z), hRb]
      exact (hone _ (face_inactive i hi0 z)).symm
  have hleft : (R.comp (collapseBoundary q b hb)).Homotopic (ContinuousMap.id (B n)) := by
    refine ⟨(show (ContinuousMap.id (B n)).Homotopy (R.comp (collapseBoundary q b hb)) from ?_).symm⟩
    exact ⟨K, hzero, fun p => (hRK p).symm⟩
  let F : C(unitInterval × stdSimplex ℝ (Fin (n + 2)), S) :=
    (collapseBoundary q b hb).comp (K.comp
      (ContinuousMap.prodMap (ContinuousMap.id _) (faceB 0)))
  have hF : ∀ t p, p ∈ boundary (Fin (n + 2)) → F (t, p) = b := by
    intro t p hp
    exact collapseBoundary_inactive q b hb _ (hpres t _ (face_zero_boundary p hp))
  let L : C(stdSimplex ℝ (Fin (n + 2)), C(unitInterval, S)) :=
    (F.comp ContinuousMap.prodSwap).curry
  have hLq : Function.FactorsThrough L q := by
    intro p r h
    ext t
    obtain rfl | ⟨hp, hr⟩ := hfiber p r h
    · rfl
    · change F (t, p) = F (t, r)
      rw [hF t p hp, hF t r hr]
  let J : C(unitInterval × S, S) :=
    (hquot.lift L hLq).uncurry.comp ContinuousMap.prodSwap
  have hJ (t : unitInterval) (p : stdSimplex ℝ (Fin (n + 2))) :
      J (t, q p) = F (t, p) := by
    exact ContinuousMap.congr_fun (ContinuousMap.congr_fun (hquot.lift_comp L hLq) p) t
  have hright : ((collapseBoundary q b hb).comp R).Homotopic (ContinuousMap.id S) := by
    refine ⟨(show (ContinuousMap.id S).Homotopy ((collapseBoundary q b hb).comp R) from ?_).symm⟩
    refine ⟨J, ?_, ?_⟩
    · intro z
      obtain ⟨p, rfl⟩ := hquot.surjective z
      change J (0, q p) = q p
      rw [hJ]
      change collapseBoundary q b hb (K (0, faceB 0 p)) = q p
      rw [hzero, collapseBoundary_zero]
    · intro z
      obtain ⟨p, rfl⟩ := hquot.surjective z
      change J (1, q p) = collapseBoundary q b hb (R (q p))
      rw [hJ]
      change collapseBoundary q b hb (K (1, faceB 0 p)) = collapseBoundary q b hb (R (q p))
      rw [← hRK, collapseBoundary_zero]
  exact ⟨⟨collapseBoundary q b hb, R, hleft, hright⟩, rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Simplex.exists_collapseBoundary_homotopyEquiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Simplex.exists_collapseBoundary_homotopyEquiv target :: scope.openDecls } }

theorem simplexSphereMap_homotopyEquiv_of_isQuotientMap
    (q : C(stdSimplex ℝ (Fin (n + 2)), S)) (b : S)
    (hb : ∀ p ∈ boundary (Fin (n + 2)), q p = b)
    (hquot : _root_.Topology.IsQuotientMap q)
    (hfiber : ∀ p r, q p = q r →
      p = r ∨ p ∈ boundary (Fin (n + 2)) ∧ r ∈ boundary (Fin (n + 2))) :
    ∃ e : _root_.ContinuousMap.HomotopyEquiv (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) S,
      e.toFun = simplexSphereMap q b hb := by
  obtain ⟨K, hK0, hK1, hKpres⟩ := exists_boundary_homotopy_collapsing_faces_through_zero n
  have hKone : ∀ p ∈ inactive n, K (1, p) = vertexZero n := by
    intro p hp
    exact Subtype.ext (hK1 p hp)
  obtain ⟨e, he⟩ := exists_collapseBoundary_homotopyEquiv q b hb hquot hfiber K hK0 hKone hKpres
  let h := stdSimplexNormedBoundarySphereHomeomorph
    (EuclideanSpace.equiv (Fin (n + 2)) ℝ).symm
  refine ⟨h.symm.toHomotopyEquiv.trans e, ?_⟩
  change e.toFun.comp (⟨h.symm, h.symm.continuous⟩ : C(_, B n)) = simplexSphereMap q b hb
  rw [he]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.simplexSphereMap_homotopyEquiv_of_isQuotientMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.simplexSphereMap_homotopyEquiv_of_isQuotientMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.simplexSphereMap_homotopyEquiv_of_isQuotientMap ``Submission.DifferentialGeometry.Simplex.simplexSphereMap_homotopyEquiv_of_isQuotientMap

end DifferentialGeometry.Simplex
