import Submission.DifferentialGeometry.Topology.Homology.Local.Manifold
import Submission.DifferentialGeometry.Topology.Homology.Relative.Reduced
import Submission.DifferentialGeometry.Topology.LocalDegree.SphereGenerator
import Submission.DifferentialGeometry.Topology.LocalDegree.SphereVanishing

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Set _root_.Metric
open scoped _root_.Manifold

namespace DifferentialGeometry.Homology

variable {k : Type} [Ring k] (R : ModuleCat k)

def localEuclideanSphereHomologyIso (n q : ℕ) :
    relativeHomology (TopCat.of (EuclideanSpace ℝ (Fin n)))
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) R (q + 1) ≅
        reducedSingularHomology R
          (TopCat.of (_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) q :=
  relativeReducedConnectingIso _ _ R q ≪≫
    reducedSingularHomologyIso R (puncturedSpaceSphereHomotopyEquiv _) q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.localEuclideanSphereHomologyIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.localEuclideanSphereHomologyIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.localEuclideanSphereHomologyIso ``Submission.DifferentialGeometry.Homology.localEuclideanSphereHomologyIso

theorem isZero_localEuclidean_succ (n q : ℕ) (h : q + 1 ≠ n) :
    _root_.CategoryTheory.Limits.IsZero (relativeHomology (TopCat.of (EuclideanSpace ℝ (Fin n)))
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) R (q + 1)) := by
  apply IsZero.of_iso _ (localEuclideanSphereHomologyIso R n q)
  cases n with
  | zero => exact isZero_reducedSingularHomology_of_isEmpty R _ q
  | succ n => exact DifferentialGeometry.LocalDegree.isZero_euclideanSphere_reducedHomology R n q (by omega)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.isZero_localEuclidean_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.isZero_localEuclidean_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.isZero_localEuclidean_succ ``Submission.DifferentialGeometry.Homology.isZero_localEuclidean_succ


theorem isZero_localEuclidean_of_gt (n q : ℕ) (h : n < q) :
    _root_.CategoryTheory.Limits.IsZero (relativeHomology (TopCat.of (EuclideanSpace ℝ (Fin n)))
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) R q) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  exact isZero_localEuclidean_succ R n q (by omega)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.isZero_localEuclidean_of_gt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.isZero_localEuclidean_of_gt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.isZero_localEuclidean_of_gt ``Submission.DifferentialGeometry.Homology.isZero_localEuclidean_of_gt

theorem not_isZero_localEuclidean_top (n : ℕ) :
    ¬IsZero (relativeHomology (TopCat.of (EuclideanSpace ℝ (Fin (n + 1))))
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (n + 1)))) (ModuleCat.of ℤ ℤ) (n + 1)) := by
  intro h
  have hz := h.of_iso (localEuclideanSphereHomologyIso (ModuleCat.of ℤ ℤ) (n + 1) n).symm
  have := ModuleCat.isZero_iff_subsingleton.mp hz
  exact DifferentialGeometry.LocalDegree.euclideanSphereTopGenerator_ne_zero n
    (Subsingleton.elim _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.not_isZero_localEuclidean_top then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.not_isZero_localEuclidean_top"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.not_isZero_localEuclidean_top ``Submission.DifferentialGeometry.Homology.not_isZero_localEuclidean_top


theorem isZero_localEuclidean_at_of_gt (n q : ℕ) (p : EuclideanSpace ℝ (Fin n)) (h : n < q) :
    _root_.CategoryTheory.Limits.IsZero (relativeHomology (TopCat.of (EuclideanSpace ℝ (Fin n)))
      ({p}ᶜ : Set (EuclideanSpace ℝ (Fin n))) R q) := by
  let e := (Homeomorph.subRight p).toOpenPartialHomeomorph
  have he : e p = 0 := sub_self p
  have hi := chartLocalHomologyIso (X := TopCat.of (EuclideanSpace ℝ (Fin n)))
    (Y := TopCat.of (EuclideanSpace ℝ (Fin n))) e p (_root_.Set.mem_univ p) R q
  rw [he] at hi
  exact (isZero_localEuclidean_of_gt R n q h).of_iso hi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.isZero_localEuclidean_at_of_gt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.isZero_localEuclidean_at_of_gt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.isZero_localEuclidean_at_of_gt ``Submission.DifferentialGeometry.Homology.isZero_localEuclidean_at_of_gt

theorem isZero_localEuclidean_at_succ (n q : ℕ) (p : EuclideanSpace ℝ (Fin n)) (h : q + 1 ≠ n) :
    _root_.CategoryTheory.Limits.IsZero (relativeHomology (TopCat.of (EuclideanSpace ℝ (Fin n)))
      ({p}ᶜ : Set (EuclideanSpace ℝ (Fin n))) R (q + 1)) := by
  let e := (Homeomorph.subRight p).toOpenPartialHomeomorph
  have he : e p = 0 := sub_self p
  have hi := chartLocalHomologyIso (X := TopCat.of (EuclideanSpace ℝ (Fin n)))
    (Y := TopCat.of (EuclideanSpace ℝ (Fin n))) e p (_root_.Set.mem_univ p) R (q + 1)
  rw [he] at hi
  exact (isZero_localEuclidean_succ R n q h).of_iso hi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.isZero_localEuclidean_at_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.isZero_localEuclidean_at_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.isZero_localEuclidean_at_succ ``Submission.DifferentialGeometry.Homology.isZero_localEuclidean_at_succ


theorem not_isZero_localEuclidean_at_top (n : ℕ) (p : EuclideanSpace ℝ (Fin (n + 1))) :
    ¬IsZero (relativeHomology (TopCat.of (EuclideanSpace ℝ (Fin (n + 1))))
      ({p}ᶜ : Set (EuclideanSpace ℝ (Fin (n + 1)))) (ModuleCat.of ℤ ℤ) (n + 1)) := by
  intro h
  let e := (Homeomorph.subRight p).toOpenPartialHomeomorph
  have he : e p = 0 := sub_self p
  have hi := chartLocalHomologyIso (X := TopCat.of (EuclideanSpace ℝ (Fin (n + 1))))
    (Y := TopCat.of (EuclideanSpace ℝ (Fin (n + 1)))) e p (_root_.Set.mem_univ p) (ModuleCat.of ℤ ℤ) (n + 1)
  rw [he] at hi
  exact not_isZero_localEuclidean_top n (h.of_iso hi.symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.not_isZero_localEuclidean_at_top then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.not_isZero_localEuclidean_at_top"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.not_isZero_localEuclidean_at_top ``Submission.DifferentialGeometry.Homology.not_isZero_localEuclidean_at_top

theorem isZero_localHalfSpace_succ {n : ℕ} [NeZero n] (p : EuclideanHalfSpace n)
    (hp : p.val 0 = 0) (q : ℕ) :
    _root_.CategoryTheory.Limits.IsZero (relativeHomology (TopCat.of (EuclideanHalfSpace n))
      ({p}ᶜ : Set (EuclideanHalfSpace n)) R (q + 1)) := by
  let := contractibleSpace_euclideanHalfSpace (n := n)
  let := contractibleSpace_puncturedHalfSpace p hp
  exact (isZero_reducedSingularHomology_of_contractible R _ q).of_iso
    (relativeReducedConnectingIso _ _ R q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.isZero_localHalfSpace_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.isZero_localHalfSpace_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.isZero_localHalfSpace_succ ``Submission.DifferentialGeometry.Homology.isZero_localHalfSpace_succ

section Manifold
variable {n : ℕ} {H M : Type} [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] [T1Space M] (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) H)
  (x : M)

theorem isZero_localManifold_interior_of_gt (hx : I.IsInteriorPoint x) (q : ℕ) (hq : n < q) :
    IsZero (relativeHomology (TopCat.of M) ({x}ᶜ : Set M) R q) := by
  let e := (DifferentialGeometry.Manifold.interiorChart I 0 x).toOpenPartialHomeomorph
  have he : x ∈ e.source := (DifferentialGeometry.Manifold.mem_interiorChart_source_iff I 0 x).mpr hx
  exact (isZero_localEuclidean_at_of_gt R n q (e x) hq).of_iso
    (chartLocalHomologyIso (X := TopCat.of M)
      (Y := TopCat.of (EuclideanSpace ℝ (Fin n))) e x he R q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.isZero_localManifold_interior_of_gt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.isZero_localManifold_interior_of_gt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.isZero_localManifold_interior_of_gt ``Submission.DifferentialGeometry.Homology.isZero_localManifold_interior_of_gt

theorem isZero_localManifold_interior_of_lt (hx : I.IsInteriorPoint x) (q : ℕ) (hq0 : q ≠ 0)
    (hq : q < n) :
    IsZero (relativeHomology (TopCat.of M) ({x}ᶜ : Set M) R q) := by
  obtain ⟨q', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq0
  let e := (DifferentialGeometry.Manifold.interiorChart I 0 x).toOpenPartialHomeomorph
  have he : x ∈ e.source := (DifferentialGeometry.Manifold.mem_interiorChart_source_iff I 0 x).mpr hx
  exact (isZero_localEuclidean_at_succ R n q' (e x) (by omega)).of_iso
    (chartLocalHomologyIso (X := TopCat.of M)
      (Y := TopCat.of (EuclideanSpace ℝ (Fin n))) e x he R (q' + 1))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.isZero_localManifold_interior_of_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.isZero_localManifold_interior_of_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.isZero_localManifold_interior_of_lt ``Submission.DifferentialGeometry.Homology.isZero_localManifold_interior_of_lt

end Manifold

section Boundary
variable {n : ℕ} [NeZero n] {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [T1Space M] (x : M)

theorem isZero_localManifold_boundary_succ (hx : (𝓡∂ n).IsBoundaryPoint x) (q : ℕ) :
    IsZero (relativeHomology (TopCat.of M) ({x}ᶜ : Set M) R (q + 1)) := by
  let : T1Space (EuclideanHalfSpace n) := inferInstanceAs
    (T1Space {v : EuclideanSpace ℝ (Fin n) // 0 ≤ v 0})
  exact (isZero_localHalfSpace_succ R (chartAt (EuclideanHalfSpace n) x x)
    (chartAt_boundary_normal_eq_zero x hx) q).of_iso
    (chartLocalHomologyIso (X := TopCat.of M) (Y := TopCat.of (EuclideanHalfSpace n))
      (chartAt (EuclideanHalfSpace n) x) x (mem_chart_source _ x) R (q + 1))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.isZero_localManifold_boundary_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.isZero_localManifold_boundary_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.isZero_localManifold_boundary_succ ``Submission.DifferentialGeometry.Homology.isZero_localManifold_boundary_succ

theorem isZero_localManifold_of_gt (q : ℕ) (hq : n < q) :
    IsZero (relativeHomology (TopCat.of M) ({x}ᶜ : Set M) R q) := by
  rcases (𝓡∂ n).isInteriorPoint_or_isBoundaryPoint x with hx | hx
  · exact isZero_localManifold_interior_of_gt R (𝓡∂ n) x hx q hq
  · obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
    exact isZero_localManifold_boundary_succ R x hx q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.isZero_localManifold_of_gt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.isZero_localManifold_of_gt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.isZero_localManifold_of_gt ``Submission.DifferentialGeometry.Homology.isZero_localManifold_of_gt

end Boundary

end DifferentialGeometry.Homology
