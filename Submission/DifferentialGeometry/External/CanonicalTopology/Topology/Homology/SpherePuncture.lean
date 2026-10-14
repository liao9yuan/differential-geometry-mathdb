import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RadialHomotopy
import Mathlib.Geometry.Manifold.Instances.Sphere

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # The actual punctured sphere and stereographic coordinates -/

noncomputable section

open _root_.ContinuousMap _root_.Set _root_.Metric
open scoped _root_.Topology

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E]

section

variable [NormedSpace ℝ E]

/-- A unit vector and its antipode are distinct. -/
theorem unitSphere_ne_antipode (v : _root_.Metric.sphere (0 : E) 1) : v ≠ -v := by
  intro h
  have he : (v : E) = -(v : E) := congrArg Subtype.val h
  have hz : (2 : ℝ) • (v : E) = 0 := by
    rw [two_smul]
    exact (congrArg (fun x : E => x + (v : E)) he).trans (neg_add_cancel _)
  have hv : (v : E) = 0 := (smul_eq_zero.mp hz).resolve_left (by norm_num)
  have hn := norm_eq_of_mem_sphere v
  rw [hv, norm_zero] at hn
  norm_num at hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.unitSphere_ne_antipode then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.unitSphere_ne_antipode"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.unitSphere_ne_antipode ``Submission.DifferentialGeometry.Topology.unitSphere_ne_antipode

end

variable [InnerProductSpace ℝ E]

/-- Stereographic projection identifies the original sphere minus its
specified pole with the actual orthogonal hyperplane. -/
def spherePunctureHomeomorph (v : _root_.Metric.sphere (0 : E) 1) :
    ({v}ᶜ : Set (_root_.Metric.sphere (0 : E) 1)) ≃ₜ (ℝ ∙ (v : E))ᗮ :=
  (stereographic (norm_eq_of_mem_sphere v)).toHomeomorphSourceTarget.trans
    (Homeomorph.Set.univ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.spherePunctureHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.spherePunctureHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.spherePunctureHomeomorph ``Submission.DifferentialGeometry.Topology.spherePunctureHomeomorph

/-- This homeomorphism uses the original stereographic map. -/
theorem spherePunctureHomeomorph_apply (v : _root_.Metric.sphere (0 : E) 1)
    (x : ({v}ᶜ : Set (_root_.Metric.sphere (0 : E) 1))) :
    spherePunctureHomeomorph v x = stereographic (norm_eq_of_mem_sphere v) x.val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.spherePunctureHomeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.spherePunctureHomeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.spherePunctureHomeomorph_apply ``Submission.DifferentialGeometry.Topology.spherePunctureHomeomorph_apply

/-- Every actual single-pole complement is contractible. -/
theorem spherePuncture_contractible (v : _root_.Metric.sphere (0 : E) 1) :
    ContractibleSpace ({v}ᶜ : Set (_root_.Metric.sphere (0 : E) 1)) :=
  (spherePunctureHomeomorph v).contractibleSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.spherePuncture_contractible then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.spherePuncture_contractible"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.spherePuncture_contractible ``Submission.DifferentialGeometry.Topology.spherePuncture_contractible


/-- The two original antipodal pole complements cover the entire sphere. -/
theorem spherePunctures_cover (v : _root_.Metric.sphere (0 : E) 1) :
    ({v}ᶜ : Set (_root_.Metric.sphere (0 : E) 1)) ∪ {-v}ᶜ = univ := by
  ext x
  simp only [_root_.Set.mem_union, _root_.Set.mem_compl_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_univ, iff_true]
  by_cases h : x = v
  · exact Or.inr (h ▸ unitSphere_ne_antipode v)
  · exact Or.inl h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.spherePunctures_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.spherePunctures_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.spherePunctures_cover ``Submission.DifferentialGeometry.Topology.spherePunctures_cover

/-- Within the opposite-pole chart, the omitted north pole is exactly
coordinate zero, so the same two-pole intersection is a punctured hyperplane. -/
def sphereDoublePunctureHomeomorph (v : _root_.Metric.sphere (0 : E) 1) :
    {x : ({-v}ᶜ : Set (_root_.Metric.sphere (0 : E) 1)) | x.val ≠ v} ≃ₜ
      ({0}ᶜ : Set (ℝ ∙ ((-v : _root_.Metric.sphere (0 : E) 1) : E))ᗮ) := by
  let p : ({-v}ᶜ : Set (_root_.Metric.sphere (0 : E) 1)) := ⟨v, unitSphere_ne_antipode v⟩
  have hp : spherePunctureHomeomorph (-v) p = 0 := stereographic_neg_apply v
  refine (spherePunctureHomeomorph (-v)).subtype (fun x => ?_)
  change (x.val ≠ v) ↔ spherePunctureHomeomorph (-v) x ≠ 0
  rw [← hp, (spherePunctureHomeomorph (-v)).injective.ne_iff]
  apply not_congr
  constructor
  · intro h
    exact Subtype.ext h
  · intro h
    exact congrArg Subtype.val h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereDoublePunctureHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereDoublePunctureHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereDoublePunctureHomeomorph ``Submission.DifferentialGeometry.Topology.sphereDoublePunctureHomeomorph

end DifferentialGeometry.Topology
