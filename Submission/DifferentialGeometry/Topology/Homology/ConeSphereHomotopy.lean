import Submission.DifferentialGeometry.Topology.Simplex.TriangleSphere
import Submission.DifferentialGeometry.Topology.Simplex.TriangleContraction
import Submission.DifferentialGeometry.Topology.Homology.TwoCycleRealization
import Submission.DifferentialGeometry.Topology.Homology.ConeEdgeHomotopy
import Submission.DifferentialGeometry.Topology.Simplex.BoundaryHomotopy
import Submission.DifferentialGeometry.Topology.Homotopy.SphereClasses

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.ContinuousMap

namespace DifferentialGeometry.Topology

open _root_.CategoryTheory _root_.AlgebraicTopology
open scoped _root_.Simplicial
universe u
variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

private def coneFaceHomotopy (x : X) (sigma : integralSingularSimplex 1 X) :
    (integralSingularSimplexEquiv 2 X (integralSingularConeTriangle x sigma)).Homotopy
      (ContinuousMap.const _ x) where
  toContinuousMap := (integralSingularSimplexEquiv 2 X
    (integralSingularConeTriangle x sigma)).comp (Simplex.vertexContraction (0 : Fin 3))
  map_zero_left p := by simp
  map_one_left p := by
    change integralSingularSimplexEquiv 2 X (integralSingularConeTriangle x sigma)
      (Simplex.vertexContraction (0 : Fin 3) (1, p)) = x
    rw [Simplex.vertexContraction_one]
    have h := integralSingularConeEdgeHomotopy_one x sigma 0
    simpa only [integralSingularConeEdgeHomotopy, ContinuousMap.comp_apply,
      ContinuousMap.coe_mk, unitInterval.symm_one, Simplex.triangleJoin_zero] using h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.coneFaceHomotopy
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.coneFaceHomotopy target :: scope.openDecls } }

private theorem coneFaceHomotopy_face_zero (x : X) (sigma : integralSingularSimplex 1 X)
    (t : unitInterval) (p : stdSimplex ℝ (Fin 2)) :
    coneFaceHomotopy x sigma (t, stdSimplex.map (0 : Fin 3).succAbove p) =
      integralSingularConeEdgeHomotopy x sigma (t, stdSimplexHomeomorphUnitInterval p) := by
  change integralSingularSimplexEquiv 2 X (integralSingularConeTriangle x sigma)
    (Simplex.vertexContraction (0 : Fin 3) (t, stdSimplex.map (0 : Fin 3).succAbove p)) = _
  rw [Simplex.vertexContraction_zero_face_zero]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.coneFaceHomotopy_face_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.coneFaceHomotopy_face_zero target :: scope.openDecls } }

private theorem coneFaceHomotopy_face_one (x : X) (sigma : integralSingularSimplex 1 X)
    (t : unitInterval) (p : stdSimplex ℝ (Fin 2)) :
    coneFaceHomotopy x sigma (t, stdSimplex.map (1 : Fin 3).succAbove p) =
      integralSingularSimplexEquiv 2 X (integralSingularConeTriangle x sigma)
        (stdSimplex.map (1 : Fin 3).succAbove
          (Simplex.vertexContraction (0 : Fin 2) (t, p))) := by
  change integralSingularSimplexEquiv 2 X (integralSingularConeTriangle x sigma)
    (Simplex.vertexContraction (0 : Fin 3) (t, stdSimplex.map (1 : Fin 3).succAbove p)) = _
  rw [Simplex.vertexContraction_zero_face_one]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.coneFaceHomotopy_face_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.coneFaceHomotopy_face_one target :: scope.openDecls } }

private theorem coneFaceHomotopy_face_two (x : X) (sigma : integralSingularSimplex 1 X)
    (t : unitInterval) (p : stdSimplex ℝ (Fin 2)) :
    coneFaceHomotopy x sigma (t, stdSimplex.map (2 : Fin 3).succAbove p) =
      integralSingularSimplexEquiv 2 X (integralSingularConeTriangle x sigma)
        (stdSimplex.map (2 : Fin 3).succAbove
          (Simplex.vertexContraction (0 : Fin 2) (t, p))) := by
  change integralSingularSimplexEquiv 2 X (integralSingularConeTriangle x sigma)
    (Simplex.vertexContraction (0 : Fin 3) (t, stdSimplex.map (2 : Fin 3).succAbove p)) = _
  rw [Simplex.vertexContraction_zero_face_two]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.coneFaceHomotopy_face_two
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.coneFaceHomotopy_face_two target :: scope.openDecls } }

theorem integralSingularConeSphereMap_homotopic_triangleSphereMap
    (x : X) (sigma : integralSingularSimplex 2 X)
    (g : C(stdSimplex ℝ (Fin 3), X))
    (hg : ∀ p ∈ Simplex.boundary (Fin 3), g p = x)
    (F : (integralSingularSimplexEquiv 2 X sigma).Homotopy g)
    (hF : ∀ (t : unitInterval) (i : Fin 3) (p : stdSimplex ℝ (Fin 2)),
      F (t, stdSimplex.map i.succAbove p) =
        integralSingularConeEdgeHomotopy x
          ((TopCat.toSSet.obj (TopCat.of X)).δ i sigma)
          (t, stdSimplexHomeomorphUnitInterval p)) :
    (integralSingularConeSphereMap x sigma).Homotopic
      (Simplex.triangleSphereMap g x hg) := by
  let f : Fin 4 → C(stdSimplex ℝ (Fin 3), X) := fun i =>
    integralSingularSimplexEquiv 2 X (integralSingularConeFaces x sigma i)
  have hf : ∀ (i : Fin 4) (j : Fin 3) (p : stdSimplex ℝ (Fin 2)),
      f i (stdSimplex.map j.succAbove p) =
        f (i.succAbove j) (stdSimplex.map (j.predAbove i).succAbove p) := by
    intro i j p
    have h := congrArg (fun a => integralSingularSimplexEquiv 1 X a p)
      (integralSingularConeFaces_compatible x sigma i j)
    change (TopCat.of X).toSSetObjEquiv _
      ((TopCat.toSSet.obj (TopCat.of X)).δ j (integralSingularConeFaces x sigma i)) p =
      (TopCat.of X).toSSetObjEquiv _
        ((TopCat.toSSet.obj (TopCat.of X)).δ (j.predAbove i)
          (integralSingularConeFaces x sigma (i.succAbove j))) p at h
    rw [TopCat.toSSetObjEquiv_δ_apply, TopCat.toSSetObjEquiv_δ_apply] at h
    exact h
  let H : ∀ i : Fin 4, (f i).Homotopy (Simplex.triangleSphereFaces g x i) :=
    Fin.cases F (fun i => coneFaceHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ i sigma))
  have hH : ∀ (i : Fin 4) (j : Fin 3) (t : unitInterval)
      (p : stdSimplex ℝ (Fin 2)), H i (t, stdSimplex.map j.succAbove p) =
        H (i.succAbove j) (t, stdSimplex.map (j.predAbove i).succAbove p) := by
    intro i j t p
    fin_cases i <;> fin_cases j
    · change F (t, stdSimplex.map (0 : Fin 3).succAbove p) =
        coneFaceHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 sigma)
          (t, stdSimplex.map (0 : Fin 3).succAbove p)
      rw [coneFaceHomotopy_face_zero]
      exact hF t 0 p
    · change F (t, stdSimplex.map (1 : Fin 3).succAbove p) =
        coneFaceHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 sigma)
          (t, stdSimplex.map (0 : Fin 3).succAbove p)
      rw [coneFaceHomotopy_face_zero]
      exact hF t 1 p
    · change F (t, stdSimplex.map (2 : Fin 3).succAbove p) =
        coneFaceHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 sigma)
          (t, stdSimplex.map (0 : Fin 3).succAbove p)
      rw [coneFaceHomotopy_face_zero]
      exact hF t 2 p
    · change coneFaceHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 sigma)
        (t, stdSimplex.map (0 : Fin 3).succAbove p) =
          F (t, stdSimplex.map (0 : Fin 3).succAbove p)
      rw [coneFaceHomotopy_face_zero]
      exact (hF t 0 p).symm
    · change coneFaceHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 sigma)
        (t, stdSimplex.map (1 : Fin 3).succAbove p) =
          coneFaceHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 sigma)
            (t, stdSimplex.map (1 : Fin 3).succAbove p)
      rw [coneFaceHomotopy_face_one, coneFaceHomotopy_face_one]
      exact hf 1 1 (Simplex.vertexContraction (0 : Fin 2) (t, p))
    · change coneFaceHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 sigma)
        (t, stdSimplex.map (2 : Fin 3).succAbove p) =
          coneFaceHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 sigma)
            (t, stdSimplex.map (1 : Fin 3).succAbove p)
      rw [coneFaceHomotopy_face_two, coneFaceHomotopy_face_one]
      exact hf 1 2 (Simplex.vertexContraction (0 : Fin 2) (t, p))
    · change coneFaceHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 sigma)
        (t, stdSimplex.map (0 : Fin 3).succAbove p) =
          F (t, stdSimplex.map (1 : Fin 3).succAbove p)
      rw [coneFaceHomotopy_face_zero]
      exact (hF t 1 p).symm
    · change coneFaceHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 sigma)
        (t, stdSimplex.map (1 : Fin 3).succAbove p) =
          coneFaceHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 sigma)
            (t, stdSimplex.map (1 : Fin 3).succAbove p)
      rw [coneFaceHomotopy_face_one, coneFaceHomotopy_face_one]
      exact hf 2 1 (Simplex.vertexContraction (0 : Fin 2) (t, p))
    · change coneFaceHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 sigma)
        (t, stdSimplex.map (2 : Fin 3).succAbove p) =
          coneFaceHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 sigma)
            (t, stdSimplex.map (2 : Fin 3).succAbove p)
      rw [coneFaceHomotopy_face_two, coneFaceHomotopy_face_two]
      exact hf 2 2 (Simplex.vertexContraction (0 : Fin 2) (t, p))
    · change coneFaceHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 sigma)
        (t, stdSimplex.map (0 : Fin 3).succAbove p) =
          F (t, stdSimplex.map (2 : Fin 3).succAbove p)
      rw [coneFaceHomotopy_face_zero]
      exact (hF t 2 p).symm
    · change coneFaceHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 sigma)
        (t, stdSimplex.map (1 : Fin 3).succAbove p) =
          coneFaceHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 sigma)
            (t, stdSimplex.map (2 : Fin 3).succAbove p)
      rw [coneFaceHomotopy_face_one, coneFaceHomotopy_face_two]
      exact hf 3 1 (Simplex.vertexContraction (0 : Fin 2) (t, p))
    · change coneFaceHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 sigma)
        (t, stdSimplex.map (2 : Fin 3).succAbove p) =
          coneFaceHomotopy x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 sigma)
            (t, stdSimplex.map (2 : Fin 3).succAbove p)
      rw [coneFaceHomotopy_face_two, coneFaceHomotopy_face_two]
      exact hf 3 2 (Simplex.vertexContraction (0 : Fin 2) (t, p))
  let B := Simplex.boundaryHomotopy hf (Simplex.triangleSphereFaces_compatible g x hg) H hH
  exact ⟨B.comp (ContinuousMap.Homotopy.refl
    ⟨(Simplex.stdSimplexNormedBoundarySphereHomeomorph
      (EuclideanSpace.equiv (Fin 3) ℝ).symm).symm,
      (Simplex.stdSimplexNormedBoundarySphereHomeomorph
        (EuclideanSpace.equiv (Fin 3) ℝ).symm).symm.continuous⟩)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularConeSphereMap_homotopic_triangleSphereMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularConeSphereMap_homotopic_triangleSphereMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularConeSphereMap_homotopic_triangleSphereMap ``Submission.DifferentialGeometry.Topology.integralSingularConeSphereMap_homotopic_triangleSphereMap

theorem integralSingularConeSphereMap_free_class_eq_triangleSphereMap
    (x : X) (sigma : integralSingularSimplex 2 X)
    (g : C(stdSimplex ℝ (Fin 3), X))
    (hg : ∀ p ∈ Simplex.boundary (Fin 3), g p = x)
    (F : (integralSingularSimplexEquiv 2 X sigma).Homotopy g)
    (hF : ∀ (t : unitInterval) (i : Fin 3) (p : stdSimplex ℝ (Fin 2)),
      F (t, stdSimplex.map i.succAbove p) =
        integralSingularConeEdgeHomotopy x
          ((TopCat.toSSet.obj (TopCat.of X)).δ i sigma)
          (t, stdSimplexHomeomorphUnitInterval p)) :
    (homotopyGroupFreeSphereEquiv 1 x).symm
      (ZerothHomotopy.mk (integralSingularConeSphereMap x sigma)) =
      (homotopyGroupFreeSphereEquiv 1 x).symm
        (ZerothHomotopy.mk (Simplex.triangleSphereMap g x hg)) := by
  apply congrArg (homotopyGroupFreeSphereEquiv 1 x).symm
  exact Quotient.sound ((homotopic_iff_joined _ _).mp
    (integralSingularConeSphereMap_homotopic_triangleSphereMap x sigma g hg F hF))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularConeSphereMap_free_class_eq_triangleSphereMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularConeSphereMap_free_class_eq_triangleSphereMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularConeSphereMap_free_class_eq_triangleSphereMap ``Submission.DifferentialGeometry.Topology.integralSingularConeSphereMap_free_class_eq_triangleSphereMap

end DifferentialGeometry.Topology
