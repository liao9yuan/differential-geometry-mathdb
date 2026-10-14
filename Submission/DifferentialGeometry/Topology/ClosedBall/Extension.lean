import Submission.DifferentialGeometry.Topology.ClosedBall.Retraction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Metric _root_.Filter
open scoped _root_.Topology
namespace DifferentialGeometry.Topology.ClosedBall
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [TopologicalSpace F]
  (a : E) {r : ℝ} (hr : 0 ≤ r)


def extension (f : C(_root_.Metric.closedBall a r, F)) : C(E, F) := f.comp (retraction a hr)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedBall.extension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedBall.extension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedBall.extension ``Submission.DifferentialGeometry.Topology.ClosedBall.extension


theorem extension_apply (f : C(_root_.Metric.closedBall a r, F)) (x : E) :
    extension a hr f x = f (retraction a hr x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedBall.extension_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedBall.extension_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedBall.extension_apply ``Submission.DifferentialGeometry.Topology.ClosedBall.extension_apply

@[simp]
theorem extension_coe (f : C(_root_.Metric.closedBall a r, F)) (x : _root_.Metric.closedBall a r) :
    extension a hr f (x : E) = f x := by
  rw [extension_apply, retraction_coe]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedBall.extension_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedBall.extension_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedBall.extension_coe ``Submission.DifferentialGeometry.Topology.ClosedBall.extension_coe

@[simp]
theorem extension_restrict (f : C(_root_.Metric.closedBall a r, F)) :
    (extension a hr f).restrict (_root_.Metric.closedBall a r) = f := by
  ext x
  exact extension_coe a hr f x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedBall.extension_restrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedBall.extension_restrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedBall.extension_restrict ``Submission.DifferentialGeometry.Topology.ClosedBall.extension_restrict

theorem extension_eventuallyEq_of_eventuallyEq (f : C(_root_.Metric.closedBall a r, F))
    {x : E} (hx : x ∈ _root_.Metric.ball a r) {g : E → F}
    (hg : (f : _root_.Metric.closedBall a r → F) =ᶠ[𝓝 (⟨x, _root_.Metric.ball_subset_closedBall hx⟩ : _root_.Metric.closedBall a r)]
      (fun y => g y.val)) :
    (extension a hr f : E → F) =ᶠ[𝓝 x] g := by
  have hρ : _root_.Filter.Tendsto (retraction a hr) (𝓝 x)
      (𝓝 (⟨x, _root_.Metric.ball_subset_closedBall hx⟩ : _root_.Metric.closedBall a r)) := by
    have h := (retraction a hr).continuous.continuousAt (x := x)
    have he := retraction_coe a hr (⟨x, _root_.Metric.ball_subset_closedBall hx⟩ : _root_.Metric.closedBall a r)
    exact he ▸ h
  have hh := hg.comp_tendsto hρ
  exact hh.trans ((retraction_eventuallyEq_id a hr hx).fun_comp g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedBall.extension_eventuallyEq_of_eventuallyEq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedBall.extension_eventuallyEq_of_eventuallyEq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedBall.extension_eventuallyEq_of_eventuallyEq ``Submission.DifferentialGeometry.Topology.ClosedBall.extension_eventuallyEq_of_eventuallyEq

theorem extension_restrict_eventuallyEq (g : C(E, F)) {x : E} (hx : x ∈ _root_.Metric.ball a r) :
    (extension a hr (g.restrict (_root_.Metric.closedBall a r)) : E → F) =ᶠ[𝓝 x] g :=
  extension_eventuallyEq_of_eventuallyEq a hr _ hx (Filter.EventuallyEq.rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedBall.extension_restrict_eventuallyEq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedBall.extension_restrict_eventuallyEq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedBall.extension_restrict_eventuallyEq ``Submission.DifferentialGeometry.Topology.ClosedBall.extension_restrict_eventuallyEq

theorem extension_ne_of_le (f : C(_root_.Metric.closedBall a r, F)) {z : F}
    (hb : ∀ y : _root_.Metric.closedBall a r, (y : E) ∈ _root_.Metric.sphere a r → f y ≠ z)
    {x : E} (hx : r ≤ _root_.Dist.dist x a) : extension a hr f x ≠ z :=
  hb (retraction a hr x) (retraction_mem_sphere a hr hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedBall.extension_ne_of_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedBall.extension_ne_of_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedBall.extension_ne_of_le ``Submission.DifferentialGeometry.Topology.ClosedBall.extension_ne_of_le

theorem extension_eq_iff (f : C(_root_.Metric.closedBall a r, F)) {z : F}
    (hb : ∀ y : _root_.Metric.closedBall a r, (y : E) ∈ _root_.Metric.sphere a r → f y ≠ z) (x : E) :
    extension a hr f x = z ↔ ∃ hx : x ∈ _root_.Metric.closedBall a r, f ⟨x, hx⟩ = z := by
  constructor
  · intro hz
    have hx : x ∈ _root_.Metric.closedBall a r := by
      by_contra hx
      exact extension_ne_of_le a hr f hb (le_of_lt (lt_of_not_ge hx)) hz
    exact ⟨hx, (extension_coe a hr f ⟨x, hx⟩).symm.trans hz⟩
  · rintro ⟨hx, hz⟩
    exact (extension_coe a hr f ⟨x, hx⟩).trans hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedBall.extension_eq_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedBall.extension_eq_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedBall.extension_eq_iff ``Submission.DifferentialGeometry.Topology.ClosedBall.extension_eq_iff

theorem extension_preimage_singleton (f : C(_root_.Metric.closedBall a r, F)) {z : F}
    (hb : ∀ y : _root_.Metric.closedBall a r, (y : E) ∈ _root_.Metric.sphere a r → f y ≠ z) :
    (extension a hr f) ⁻¹' {z} = Subtype.val '' (f ⁻¹' {z}) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hmem, hz⟩ := (extension_eq_iff a hr f hb x).mp hx
    exact ⟨⟨x, hmem⟩, hz, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact (extension_coe a hr f y).trans hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedBall.extension_preimage_singleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedBall.extension_preimage_singleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedBall.extension_preimage_singleton ``Submission.DifferentialGeometry.Topology.ClosedBall.extension_preimage_singleton


theorem extension_preimage_singleton_subset_ball (f : C(_root_.Metric.closedBall a r, F)) {z : F}
    (hb : ∀ y : _root_.Metric.closedBall a r, (y : E) ∈ _root_.Metric.sphere a r → f y ≠ z) :
    (extension a hr f) ⁻¹' {z} ⊆ _root_.Metric.ball a r := by
  intro x hx
  exact lt_of_not_ge (fun hle => extension_ne_of_le a hr f hb hle hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedBall.extension_preimage_singleton_subset_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedBall.extension_preimage_singleton_subset_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedBall.extension_preimage_singleton_subset_ball ``Submission.DifferentialGeometry.Topology.ClosedBall.extension_preimage_singleton_subset_ball

variable [Zero F]


theorem extension_ne_zero_of_not_mem (f : C(_root_.Metric.closedBall a r, F))
    (hb : ∀ y : _root_.Metric.closedBall a r, (y : E) ∈ _root_.Metric.sphere a r → f y ≠ 0)
    {x : E} (hx : x ∉ _root_.Metric.closedBall a r) : extension a hr f x ≠ 0 :=
  extension_ne_of_le a hr f hb (le_of_lt (lt_of_not_ge hx))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedBall.extension_ne_zero_of_not_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedBall.extension_ne_zero_of_not_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedBall.extension_ne_zero_of_not_mem ``Submission.DifferentialGeometry.Topology.ClosedBall.extension_ne_zero_of_not_mem

theorem extension_zeroSet (f : C(_root_.Metric.closedBall a r, F))
    (hb : ∀ y : _root_.Metric.closedBall a r, (y : E) ∈ _root_.Metric.sphere a r → f y ≠ 0) :
    {x : E | extension a hr f x = 0} =
      Subtype.val '' {y : _root_.Metric.closedBall a r | f y = 0} :=
  extension_preimage_singleton a hr f hb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedBall.extension_zeroSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedBall.extension_zeroSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedBall.extension_zeroSet ``Submission.DifferentialGeometry.Topology.ClosedBall.extension_zeroSet

end DifferentialGeometry.Topology.ClosedBall
