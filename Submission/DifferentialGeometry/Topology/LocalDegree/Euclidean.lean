import Submission.DifferentialGeometry.Topology.LocalDegree.IsolatedZero
import Submission.DifferentialGeometry.Topology.LocalDegree.SphereDegree

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.Filter _root_.Metric _root_.Set
open scoped _root_.Topology
noncomputable section
namespace DifferentialGeometry.LocalDegree
variable {d : ℕ}


theorem euclideanSphereDegree_sphereMap_eq
    (f : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)))
    (x : EuclideanSpace ℝ (Fin (d + 1))) (R : ℝ)
    (hf : ContinuousOn f (_root_.Metric.closedBall x R))
    (hz : ∀ y ∈ _root_.Metric.closedBall x R, y ≠ x → f y ≠ 0) (r₀ r₁ : _root_.Set.Ioc (0 : ℝ) R) :
    euclideanSphereDegree (sphereMap f x R hf hz r₀) =
      euclideanSphereDegree (sphereMap f x R hf hz r₁) :=
  euclideanSphereDegree_eq_of_homotopy (sphereMapHomotopy f x R hf hz r₀ r₁)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanSphereDegree_sphereMap_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanSphereDegree_sphereMap_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanSphereDegree_sphereMap_eq ``Submission.DifferentialGeometry.LocalDegree.euclideanSphereDegree_sphereMap_eq

private def radiusSphereMap
    {f : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {x : EuclideanSpace ℝ (Fin (d + 1))} {R : ℝ} (h : IsolatingRadius f x R) :
    C(EuclideanSphere d, EuclideanSphere d) :=
  sphereMap f x R h.continuousOn h.nonzero ⟨R, h.pos, le_rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.radiusSphereMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.radiusSphereMap target :: scope.openDecls } }

private theorem radius_degree_eq
    {f : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {x : EuclideanSpace ℝ (Fin (d + 1))} {R S : ℝ}
    (hR : IsolatingRadius f x R) (hS : IsolatingRadius f x S) :
    euclideanSphereDegree (radiusSphereMap hR) = euclideanSphereDegree (radiusSphereMap hS) := by
  let r : ℝ := _root_.Min.min R S
  have hr : 0 < r := lt_min hR.pos hS.pos
  have hrR : r ≤ R := min_le_left _ _
  have hrS : r ≤ S := min_le_right _ _
  calc
    euclideanSphereDegree (radiusSphereMap hR) =
        euclideanSphereDegree (sphereMap f x R hR.continuousOn hR.nonzero ⟨r, hr, hrR⟩) :=
      euclideanSphereDegree_sphereMap_eq _ _ _ _ _ _ _
    _ = euclideanSphereDegree (sphereMap f x S hS.continuousOn hS.nonzero ⟨r, hr, hrS⟩) := by
      congr 1
    _ = euclideanSphereDegree (radiusSphereMap hS) :=
      euclideanSphereDegree_sphereMap_eq _ _ _ _ _ _ _

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.radius_degree_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.radius_degree_eq target :: scope.openDecls } }

def euclideanLocalDegree
    (f : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)))
    (x : EuclideanSpace ℝ (Fin (d + 1))) (h : isolatedZero f x) : ℤ :=
  euclideanSphereDegree (radiusSphereMap h.choose_spec)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanLocalDegree then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanLocalDegree"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanLocalDegree ``Submission.DifferentialGeometry.LocalDegree.euclideanLocalDegree


theorem euclideanLocalDegree_eq_sphereDegree
    {f : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {x : EuclideanSpace ℝ (Fin (d + 1))} (h : isolatedZero f x)
    {R : ℝ} (hR : IsolatingRadius f x R) (r : _root_.Set.Ioc (0 : ℝ) R) :
    euclideanLocalDegree f x h =
      euclideanSphereDegree (sphereMap f x R hR.continuousOn hR.nonzero r) :=
  (radius_degree_eq h.choose_spec hR).trans
    (euclideanSphereDegree_sphereMap_eq _ _ _ _ _ _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanLocalDegree_eq_sphereDegree then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanLocalDegree_eq_sphereDegree"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanLocalDegree_eq_sphereDegree ``Submission.DifferentialGeometry.LocalDegree.euclideanLocalDegree_eq_sphereDegree


theorem euclideanLocalDegree_generator
    {f : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {x : EuclideanSpace ℝ (Fin (d + 1))} (h : isolatedZero f x)
    {R : ℝ} (hR : IsolatingRadius f x R) (r : _root_.Set.Ioc (0 : ℝ) R) :
    DifferentialGeometry.Homology.reducedSingularHomologyMap (ModuleCat.of ℤ ℤ)
        (TopCat.ofHom (sphereMap f x R hR.continuousOn hR.nonzero r)) d
          (euclideanSphereTopGenerator d) =
      euclideanLocalDegree f x h • euclideanSphereTopGenerator d := by
  rw [euclideanLocalDegree_eq_sphereDegree h hR r]
  exact euclideanSphereDegree_generator _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanLocalDegree_generator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanLocalDegree_generator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanLocalDegree_generator ``Submission.DifferentialGeometry.LocalDegree.euclideanLocalDegree_generator


theorem euclideanLocalDegree_congr
    {f g : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {x : EuclideanSpace ℝ (Fin (d + 1))}
    (hf : isolatedZero f x) (hg : isolatedZero g x) (hfg : f =ᶠ[𝓝 x] g) :
    euclideanLocalDegree f x hf = euclideanLocalDegree g x hg := by
  let R := hf.choose
  have hR : IsolatingRadius f x R := hf.choose_spec
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hfg
  let r := _root_.Min.min R (ε / 2)
  have hr : 0 < r := lt_min hR.pos (by positivity)
  have hrr : r ≤ R := min_le_left _ _
  have heq : _root_.Set.EqOn f g (_root_.Metric.closedBall x r) := fun y hy ↦
    hball (_root_.Metric.closedBall_subset_ball (lt_of_le_of_lt (min_le_right _ _) (by linarith)) hy)
  have hfr := hR.mono hr hrr
  have hgr := hfr.congr heq
  rw [euclideanLocalDegree_eq_sphereDegree hf hfr ⟨r, hr, le_rfl⟩,
    euclideanLocalDegree_eq_sphereDegree hg hgr ⟨r, hr, le_rfl⟩]
  congr 1
  apply ContinuousMap.ext
  intro v
  apply Subtype.ext
  simp only [sphereMap_apply]
  rw [heq (by
    rw [_root_.Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hr.le, norm_eq_of_mem_sphere v, mul_one])]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanLocalDegree_congr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanLocalDegree_congr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanLocalDegree_congr ``Submission.DifferentialGeometry.LocalDegree.euclideanLocalDegree_congr


theorem isolatedZero_euclidean_id :
    isolatedZero (fun y : EuclideanSpace ℝ (Fin (d + 1)) => y) 0 :=
  ⟨1, ⟨by norm_num, continuousOn_id, fun _ _ => Iff.rfl⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.isolatedZero_euclidean_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.isolatedZero_euclidean_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.isolatedZero_euclidean_id ``Submission.DifferentialGeometry.LocalDegree.isolatedZero_euclidean_id


@[simp]
theorem euclideanLocalDegree_id :
    euclideanLocalDegree (fun y : EuclideanSpace ℝ (Fin (d + 1)) => y) 0
      isolatedZero_euclidean_id = 1 := by
  have hR : IsolatingRadius (fun y : EuclideanSpace ℝ (Fin (d + 1)) => y) 0 1 :=
    ⟨by norm_num, continuousOn_id, fun _ _ => Iff.rfl⟩
  rw [euclideanLocalDegree_eq_sphereDegree isolatedZero_euclidean_id hR ⟨1, by norm_num, le_rfl⟩]
  change euclideanSphereDegree (sphereMap (fun y : EuclideanSpace ℝ (Fin (d + 1)) => y)
    0 1 continuousOn_id (fun _ _ h => h) ⟨1, by norm_num, le_rfl⟩) = 1
  rw [sphereMap_id, euclideanSphereDegree_id]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanLocalDegree_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanLocalDegree_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanLocalDegree_id ``Submission.DifferentialGeometry.LocalDegree.euclideanLocalDegree_id

end DifferentialGeometry.LocalDegree
