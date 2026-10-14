import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Homology

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology _root_.Bundle _root_.Manifold _root_.Set
open scoped _root_.Simplicial _root_.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M]

def existsFundamentalClassAt (o : TangentOrientationSection M) (x : M) : Prop :=
  ∃ z : IntegralHomology M 3, absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.existsFundamentalClassAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.existsFundamentalClassAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.existsFundamentalClassAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.existsFundamentalClassAt

def localClassRealizationLocallyConstant (o : TangentOrientationSection M) : Prop :=
  ∀ (z : IntegralHomology M 3) (x : M), ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
    ∀ y ∈ U, (absoluteToRelative M ({y}ᶜ) 3 z = localOrientationClass o y ↔
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localClassRealizationLocallyConstant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localClassRealizationLocallyConstant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localClassRealizationLocallyConstant ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localClassRealizationLocallyConstant

theorem existsFundamentalClassAt_iff_mem_range (o : TangentOrientationSection M) (x : M) :
    existsFundamentalClassAt o x ↔
      localOrientationClass o x ∈ Set.range (absoluteToRelative M ({x}ᶜ) 3) :=
  Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.existsFundamentalClassAt_iff_mem_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.existsFundamentalClassAt_iff_mem_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.existsFundamentalClassAt_iff_mem_range ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.existsFundamentalClassAt_iff_mem_range

theorem exists_fundamentalClassAt_iff_surjective (o : TangentOrientationSection M) (x : M)
    (hgen : Function.Surjective (fun z : ℤ => z • localOrientationClass o x)) :
    existsFundamentalClassAt o x ↔ Function.Surjective (absoluteToRelative M ({x}ᶜ) 3) := by
  constructor
  · rintro ⟨z, hz⟩ w
    obtain ⟨m, hm⟩ := hgen w
    exact ⟨m • z, by rw [map_zsmul, hz]; exact hm⟩
  · intro h
    exact h (localOrientationClass o x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_fundamentalClassAt_iff_surjective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_fundamentalClassAt_iff_surjective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_fundamentalClassAt_iff_surjective ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_fundamentalClassAt_iff_surjective

theorem existsFundamentalClassAt_of_forall (o : TangentOrientationSection M)
    (h : ∃ z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x) (x : M) :
    existsFundamentalClassAt o x :=
  ⟨h.choose, h.choose_spec x⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.existsFundamentalClassAt_of_forall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.existsFundamentalClassAt_of_forall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.existsFundamentalClassAt_of_forall ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.existsFundamentalClassAt_of_forall

theorem finite_realization_of_forall (o : TangentOrientationSection M)
    (h : ∃ z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x) (F : Finset M) :
    ∃ z : IntegralHomology M 3, ∀ x ∈ F,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x :=
  ⟨h.choose, fun x _ => h.choose_spec x⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.finite_realization_of_forall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.finite_realization_of_forall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.finite_realization_of_forall ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.finite_realization_of_forall

variable [ConnectedSpace M]

theorem exists_fundamentalClass_of_local_realization_at (o : TangentOrientationSection M)
    (hprop : localClassRealizationLocallyConstant o) (x₀ : M) (h : existsFundamentalClassAt o x₀) :
    ∃ z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x := by
  obtain ⟨z, hz⟩ := h
  let S : Set M := {x | absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x}
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨U, hU, hxU, hconst⟩ := hprop z x
    exact Filter.mem_of_superset (hU.mem_nhds hxU) fun y hy => (hconst y hy).mpr hx
  have hSclosed : IsClosed S := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨U, hU, hxU, hconst⟩ := hprop z x
    exact Filter.mem_of_superset (hU.mem_nhds hxU) fun y hy hyS => hx ((hconst y hy).mp hyS)
  have hSuniv : S = univ := IsClopen.eq_univ ⟨hSclosed, hSopen⟩ ⟨x₀, hz⟩
  refine ⟨z, fun x => ?_⟩
  have : x ∈ S := by rw [hSuniv]; trivial
  exact this

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_fundamentalClass_of_local_realization_at then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_fundamentalClass_of_local_realization_at"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_fundamentalClass_of_local_realization_at ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_fundamentalClass_of_local_realization_at

theorem exists_fundamentalClass_of_local_realization (o : TangentOrientationSection M)
    (hprop : localClassRealizationLocallyConstant o) (x₀ : M)
    (h : ∀ x : M, existsFundamentalClassAt o x) :
    ∃ z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x :=
  exists_fundamentalClass_of_local_realization_at o hprop x₀ (h x₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_fundamentalClass_of_local_realization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_fundamentalClass_of_local_realization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_fundamentalClass_of_local_realization ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_fundamentalClass_of_local_realization

theorem exists_fundamentalClass_of_finite_realization (o : TangentOrientationSection M)
    (hprop : localClassRealizationLocallyConstant o) (x₀ : M)
    (h : ∀ F : Finset M, ∃ z : IntegralHomology M 3, ∀ x ∈ F,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x) :
    ∃ z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x := by
  obtain ⟨z, hz⟩ := h {x₀}
  exact exists_fundamentalClass_of_local_realization_at o hprop x₀
    ⟨z, hz x₀ (Finset.mem_singleton_self x₀)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_fundamentalClass_of_finite_realization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_fundamentalClass_of_finite_realization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_fundamentalClass_of_finite_realization ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_fundamentalClass_of_finite_realization

theorem finite_realization_iff_existsFundamentalClassAt (o : TangentOrientationSection M)
    (hprop : localClassRealizationLocallyConstant o) (x₀ : M) :
    (∀ F : Finset M, ∃ z : IntegralHomology M 3, ∀ x ∈ F,
        absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x) ↔
      existsFundamentalClassAt o x₀ := by
  constructor
  · intro h
    obtain ⟨z, hz⟩ := h {x₀}
    exact ⟨z, hz x₀ (Finset.mem_singleton_self x₀)⟩
  · intro h
    exact finite_realization_of_forall o
      (exists_fundamentalClass_of_local_realization_at o hprop x₀ h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.finite_realization_iff_existsFundamentalClassAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.finite_realization_iff_existsFundamentalClassAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.finite_realization_iff_existsFundamentalClassAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.finite_realization_iff_existsFundamentalClassAt

theorem exists_unique_fundamentalClass_of_local_realization (o : TangentOrientationSection M)
    (hprop : localClassRealizationLocallyConstant o) (x₀ : M) (h : existsFundamentalClassAt o x₀)
    (hinj : Function.Injective (absoluteToRelative M ({x₀}ᶜ) 3)) :
    ∃! z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x :=
  exists_unique_fundamentalClass_of_exists o
    (exists_fundamentalClass_of_local_realization_at o hprop x₀ h) ⟨x₀, hinj⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_unique_fundamentalClass_of_local_realization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_unique_fundamentalClass_of_local_realization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_unique_fundamentalClass_of_local_realization ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_unique_fundamentalClass_of_local_realization

omit [ConnectedSpace M] in
theorem exists_unique_fundamentalClass_of_exists_of_subsingleton [T2Space M] [CompactSpace M]
    (o : TangentOrientationSection M) (x : M)
    (h : ∃ z : IntegralHomology M 3, ∀ y : M,
      absoluteToRelative M ({y}ᶜ) 3 z = localOrientationClass o y)
    (hsub : Subsingleton (IntegralHomology ({x}ᶜ : Set M) 3)) :
    ∃! z : IntegralHomology M 3, ∀ y : M,
      absoluteToRelative M ({y}ᶜ) 3 z = localOrientationClass o y :=
  exists_unique_fundamentalClass_of_exists o h
    ⟨x, absoluteToRelative_compl_singleton_injective_of_subsingleton x hsub⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_unique_fundamentalClass_of_exists_of_subsingleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_unique_fundamentalClass_of_exists_of_subsingleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_unique_fundamentalClass_of_exists_of_subsingleton ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_unique_fundamentalClass_of_exists_of_subsingleton

omit [ConnectedSpace M] in
theorem fundamentalClass_generator_of_subsingleton [T2Space M] [CompactSpace M]
    (o : TangentOrientationSection M) (x : M)
    (hlocal : Function.Bijective (fun z : ℤ => z • localOrientationClass o x))
    (hsub : Subsingleton (IntegralHomology ({x}ᶜ : Set M) 3)) :
    Function.Bijective (fun z : ℤ => z • fundamentalClass o) :=
  fundamentalClass_generator_of o x hlocal
    (absoluteToRelative_compl_singleton_injective_of_subsingleton x hsub)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.fundamentalClass_generator_of_subsingleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.fundamentalClass_generator_of_subsingleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.fundamentalClass_generator_of_subsingleton ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.fundamentalClass_generator_of_subsingleton

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
