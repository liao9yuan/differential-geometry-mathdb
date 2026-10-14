import Submission.DifferentialGeometry.Topology.Simplex.BoundaryGluing

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.Simplex

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

def simplexSphereFaces (g : C(stdSimplex ℝ (Fin (n + 2)), X)) (x : X) :
    Fin (n + 3) → C(stdSimplex ℝ (Fin (n + 2)), X) :=
  Fin.cons g (fun _ => ContinuousMap.const _ x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.simplexSphereFaces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.simplexSphereFaces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.simplexSphereFaces ``Submission.DifferentialGeometry.Simplex.simplexSphereFaces

@[simp] theorem simplexSphereFaces_zero (g : C(stdSimplex ℝ (Fin (n + 2)), X))
    (x : X) : simplexSphereFaces g x 0 = g := by
  exact Fin.cons_zero _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.simplexSphereFaces_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.simplexSphereFaces_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.simplexSphereFaces_zero ``Submission.DifferentialGeometry.Simplex.simplexSphereFaces_zero

@[simp] theorem simplexSphereFaces_succ (g : C(stdSimplex ℝ (Fin (n + 2)), X))
    (x : X) (i : Fin (n + 2)) :
    simplexSphereFaces g x i.succ = ContinuousMap.const _ x := by
  exact Fin.cons_succ _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.simplexSphereFaces_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.simplexSphereFaces_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.simplexSphereFaces_succ ``Submission.DifferentialGeometry.Simplex.simplexSphereFaces_succ

theorem simplexSphereFaces_compatible (g : C(stdSimplex ℝ (Fin (n + 2)), X)) (x : X)
    (hg : ∀ p ∈ boundary (Fin (n + 2)), g p = x)
    (i : Fin (n + 3)) (j : Fin (n + 2)) (p : stdSimplex ℝ (Fin (n + 1))) :
    simplexSphereFaces g x i (stdSimplex.map j.succAbove p) =
      simplexSphereFaces g x (i.succAbove j)
        (stdSimplex.map (j.predAbove i).succAbove p) := by
  have h (k : Fin (n + 2)) : g (stdSimplex.map k.succAbove p) = x :=
    hg _ ⟨k, map_succAbove_apply_pivot k p⟩
  induction i using Fin.cases with
  | zero => simpa only [simplexSphereFaces_zero, Fin.succAbove_zero,
      simplexSphereFaces_succ, ContinuousMap.const_apply] using h j
  | succ i =>
      induction j using Fin.cases with
      | zero =>
          simpa only [simplexSphereFaces_succ, ContinuousMap.const_apply,
            Fin.succ_succAbove_zero, simplexSphereFaces_zero] using (h (Fin.predAbove 0 i.succ)).symm
      | succ j =>
          simp only [simplexSphereFaces_succ, ContinuousMap.const_apply,
            Fin.succ_succAbove_succ]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.simplexSphereFaces_compatible then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.simplexSphereFaces_compatible"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.simplexSphereFaces_compatible ``Submission.DifferentialGeometry.Simplex.simplexSphereFaces_compatible

def simplexSphereMap (g : C(stdSimplex ℝ (Fin (n + 2)), X)) (x : X)
    (hg : ∀ p ∈ boundary (Fin (n + 2)), g p = x) :
    C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X) :=
  boundarySphereDesc (simplexSphereFaces g x) (simplexSphereFaces_compatible g x hg)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.simplexSphereMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.simplexSphereMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.simplexSphereMap ``Submission.DifferentialGeometry.Simplex.simplexSphereMap

theorem simplexSphereMap_face (g : C(stdSimplex ℝ (Fin (n + 2)), X)) (x : X)
    (hg : ∀ p ∈ boundary (Fin (n + 2)), g p = x)
    (i : Fin (n + 3)) (p : stdSimplex ℝ (Fin (n + 2))) :
    simplexSphereMap g x hg
      (stdSimplexNormedBoundarySphereHomeomorph
        (EuclideanSpace.equiv (Fin (n + 2)) ℝ).symm
        ⟨stdSimplex.map i.succAbove p, ⟨i, map_succAbove_apply_pivot i p⟩⟩) =
      simplexSphereFaces g x i p :=
  boundarySphereDesc_face (simplexSphereFaces g x) (simplexSphereFaces_compatible g x hg) i p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.simplexSphereMap_face then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.simplexSphereMap_face"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.simplexSphereMap_face ``Submission.DifferentialGeometry.Simplex.simplexSphereMap_face

end DifferentialGeometry.Simplex

namespace DifferentialGeometry.Simplex

open _root_.ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem simplexSphereMap_natural {n : ℕ} (g : C(stdSimplex ℝ (Fin (n + 2)), X)) (x : X)
    (hg : ∀ p ∈ boundary (Fin (n + 2)), g p = x) (f : C(X, Y)) :
    simplexSphereMap (f.comp g) (f x) (fun p hp => congrArg f (hg p hp)) =
      f.comp (simplexSphereMap g x hg) := by
  ext z
  obtain ⟨p, rfl⟩ := (stdSimplexNormedBoundarySphereHomeomorph
    (EuclideanSpace.equiv (Fin (n + 2)) ℝ).symm).surjective z
  obtain ⟨i, hi⟩ := p.property
  let q := faceDelete i ⟨p.val, hi⟩
  have he : p = ⟨stdSimplex.map i.succAbove q,
      ⟨i, map_succAbove_apply_pivot i q⟩⟩ := by
    apply Subtype.ext
    exact (congrArg Subtype.val (faceInsert_faceDelete i ⟨p.val, hi⟩)).symm
  rw [he]
  change simplexSphereMap _ _ _ _ = f (simplexSphereMap _ _ _ _)
  rw [simplexSphereMap_face, simplexSphereMap_face]
  induction i using Fin.cases with
  | zero => rw [simplexSphereFaces_zero, simplexSphereFaces_zero, _root_.ContinuousMap.comp_apply]
  | succ i => rw [simplexSphereFaces_succ, simplexSphereFaces_succ, _root_.ContinuousMap.const_apply, _root_.ContinuousMap.const_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.simplexSphereMap_natural then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.simplexSphereMap_natural"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.simplexSphereMap_natural ``Submission.DifferentialGeometry.Simplex.simplexSphereMap_natural

end DifferentialGeometry.Simplex
