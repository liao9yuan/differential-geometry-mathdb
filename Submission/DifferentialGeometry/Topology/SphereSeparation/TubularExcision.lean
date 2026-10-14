import Submission.DifferentialGeometry.Topology.SphereSeparation.BicollarRelativeHomology
import Submission.DifferentialGeometry.Topology.SphereSeparation.TopologicalRelativeUnion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.Set
open _root_.Topology

namespace DifferentialGeometry.Topology.SphereSeparation

noncomputable def openBicollarExcisionAmbientHomeomorph
    {a : ℝ} (Φ : SphereTwo × AxialInterval a → EuclideanThree)
    (hΦ : _root_.Topology.IsOpenEmbedding Φ) :
    SphereTwo × AxialInterval a ≃ₜ
      (((Set.range Φ)ᶜ)ᶜ : Set EuclideanThree) :=
  hΦ.isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (by simp))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.openBicollarExcisionAmbientHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.openBicollarExcisionAmbientHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.openBicollarExcisionAmbientHomeomorph ``Submission.DifferentialGeometry.Topology.SphereSeparation.openBicollarExcisionAmbientHomeomorph

@[simp]
theorem openBicollarExcisionAmbientHomeomorph_coe
    {a : ℝ} (Φ : SphereTwo × AxialInterval a → EuclideanThree)
    (hΦ : _root_.Topology.IsOpenEmbedding Φ) (x : SphereTwo × AxialInterval a) :
    ((openBicollarExcisionAmbientHomeomorph Φ hΦ x :
      (((Set.range Φ)ᶜ)ᶜ : Set EuclideanThree)) : EuclideanThree) = Φ x :=
  by
    simp only [openBicollarExcisionAmbientHomeomorph,
      Homeomorph.trans_apply]
    exact hΦ.isEmbedding.toHomeomorph_apply_coe x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.openBicollarExcisionAmbientHomeomorph_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.openBicollarExcisionAmbientHomeomorph_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.openBicollarExcisionAmbientHomeomorph_coe ``Submission.DifferentialGeometry.Topology.SphereSeparation.openBicollarExcisionAmbientHomeomorph_coe

noncomputable def openBicollarExcisionSubspaceHomeomorph
    {a : ℝ} (ha : 0 < a)
    (e : SphereTwo → EuclideanThree)
    (Φ : SphereTwo × AxialInterval a → EuclideanThree)
    (hΦ : _root_.Topology.IsOpenEmbedding Φ)
    (hzero : ∀ p, Φ (p, axialZero ha) = e p) :
    ((zeroSliceDomain ha)ᶜ : Set (SphereTwo × AxialInterval a)) ≃ₜ
      subspaceOutside (Set.range e)ᶜ (Set.range Φ)ᶜ := by
  let h := openBicollarExcisionAmbientHomeomorph Φ hΦ
  apply h.subtype
  intro x
  change x ∉ zeroSliceDomain ha ↔ (h x).1 ∉ Set.range e
  rw [show (h x).1 = Φ x by
    exact openBicollarExcisionAmbientHomeomorph_coe Φ hΦ x]
  constructor
  · intro hx hxe
    rcases hxe with ⟨p, hp⟩
    have hp' : Φ x = Φ (p, axialZero ha) := by
      rw [hzero p]
      exact hp.symm
    have : x = (p, axialZero ha) := hΦ.injective hp'
    apply hx
    rw [this]
    exact ⟨Set.mem_univ _, rfl⟩
  · intro hx hxslice
    apply hx
    rcases hxslice with ⟨-, haxial⟩
    refine ⟨x.1, ?_⟩
    rw [← hzero x.1]
    congr
    exact haxial.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.openBicollarExcisionSubspaceHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.openBicollarExcisionSubspaceHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.openBicollarExcisionSubspaceHomeomorph ``Submission.DifferentialGeometry.Topology.SphereSeparation.openBicollarExcisionSubspaceHomeomorph


theorem range_subset_openBicollar_range
    {a : ℝ} (ha : 0 < a)
    (e : SphereTwo → EuclideanThree)
    (Φ : SphereTwo × AxialInterval a → EuclideanThree)
    (hzero : ∀ p, Φ (p, axialZero ha) = e p) :
    Set.range e ⊆ Set.range Φ := by
  rintro _ ⟨p, rfl⟩
  exact ⟨(p, axialZero ha), hzero p⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.range_subset_openBicollar_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.range_subset_openBicollar_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.range_subset_openBicollar_range ``Submission.DifferentialGeometry.Topology.SphereSeparation.range_subset_openBicollar_range

theorem openBicollar_excision_condition
    {a : ℝ} (ha : 0 < a)
    (e : SphereTwo → EuclideanThree)
    (Φ : SphereTwo × AxialInterval a → EuclideanThree)
    (hΦ : _root_.Topology.IsOpenEmbedding Φ)
    (hzero : ∀ p, Φ (p, axialZero ha) = e p) :
    closure (Set.range Φ)ᶜ ⊆ interior (Set.range e)ᶜ := by
  have hecont : Continuous e := by
    have hsection : Continuous
        (fun p : SphereTwo ↦ (p, axialZero ha)) := by fun_prop
    have hcomp : Continuous (fun p : SphereTwo ↦ Φ (p, axialZero ha)) :=
      hΦ.continuous.comp hsection
    simpa only [hzero] using hcomp
  have heclosed : IsClosed (Set.range e) :=
    (isCompact_range hecont).isClosed
  rw [hΦ.isOpen_range.isClosed_compl.closure_eq,
    heclosed.isOpen_compl.interior_eq]
  exact compl_subset_compl.mpr
    (range_subset_openBicollar_range ha e Φ hzero)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.openBicollar_excision_condition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.openBicollar_excision_condition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.openBicollar_excision_condition ``Submission.DifferentialGeometry.Topology.SphereSeparation.openBicollar_excision_condition

theorem isIso_openBicollar_relativeSingularHomologyMap
    {a : ℝ} (ha : 0 < a)
    (e : SphereTwo → EuclideanThree)
    (Φ : SphereTwo × AxialInterval a → EuclideanThree)
    (hΦ : _root_.Topology.IsOpenEmbedding Φ)
    (hzero : ∀ p, Φ (p, axialZero ha) = e p)
    (n : ℕ) :
    _root_.CategoryTheory.IsIso
      (relativeSingularHomologyMapOfSubspaces
        ⟨openBicollarExcisionAmbientHomeomorph Φ hΦ,
          (openBicollarExcisionAmbientHomeomorph Φ hΦ).continuous⟩
        ((zeroSliceDomain ha)ᶜ :
          Set (SphereTwo × AxialInterval a))
        (subspaceOutside (Set.range e)ᶜ (Set.range Φ)ᶜ)
        (fun x hx ↦
          (openBicollarExcisionSubspaceHomeomorph
            ha e Φ hΦ hzero ⟨x, hx⟩).2)
        n) := by
  apply isIso_relativeSingularHomologyMapOfSubspaces
  · exact (openBicollarExcisionAmbientHomeomorph Φ hΦ).isHomeomorph
  · let g := openBicollarExcisionSubspaceHomeomorph
      ha e Φ hΦ hzero
    convert g.isHomeomorph using 1
    funext x
    apply Subtype.ext
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.isIso_openBicollar_relativeSingularHomologyMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.isIso_openBicollar_relativeSingularHomologyMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.isIso_openBicollar_relativeSingularHomologyMap ``Submission.DifferentialGeometry.Topology.SphereSeparation.isIso_openBicollar_relativeSingularHomologyMap

theorem embeddedSphere_relativeH1_iso_int_of_openBicollar_of_sphereH1
    {a : ℝ} (ha : 0 < a)
    (e : SphereTwo → EuclideanThree)
    (Φ : SphereTwo × AxialInterval a → EuclideanThree)
    (hΦ : _root_.Topology.IsOpenEmbedding Φ)
    (hzero : ∀ p, Φ (p, axialZero ha) = e p)
    (hSphere : _root_.CategoryTheory.Limits.IsZero
      (integerSingularHomology (TopCat.of SphereTwo) 1)) :
    Nonempty
      (relativeSingularHomologyOfSubspace (Set.range e)ᶜ 1 ≅
        ModuleCat.of ℤ ℤ) := by
  let pairMap := relativeSingularHomologyMapOfSubspaces
    ⟨openBicollarExcisionAmbientHomeomorph Φ hΦ,
      (openBicollarExcisionAmbientHomeomorph Φ hΦ).continuous⟩
    ((zeroSliceDomain ha)ᶜ : Set (SphereTwo × AxialInterval a))
    (subspaceOutside (Set.range e)ᶜ (Set.range Φ)ᶜ)
    (fun x hx ↦
      (openBicollarExcisionSubspaceHomeomorph
        ha e Φ hΦ hzero ⟨x, hx⟩).2)
    1
  let _ : _root_.CategoryTheory.IsIso pairMap :=
    isIso_openBicollar_relativeSingularHomologyMap
      ha e Φ hΦ hzero 1
  let excisionMap := excisionRelativeSingularHomologyMap
    (Set.range e)ᶜ (Set.range Φ)ᶜ 1
  let _ : _root_.CategoryTheory.IsIso excisionMap :=
    singularExcisionFor (Set.range e)ᶜ (Set.range Φ)ᶜ
      (openBicollar_excision_condition ha e Φ hΦ hzero) 1
  exact ⟨(_root_.CategoryTheory.asIso excisionMap).symm ≪≫ (_root_.CategoryTheory.asIso pairMap).symm ≪≫
    Classical.choice
      (centralSliceComplement_relativeH1_iso_int_of_sphere ha hSphere)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.embeddedSphere_relativeH1_iso_int_of_openBicollar_of_sphereH1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.embeddedSphere_relativeH1_iso_int_of_openBicollar_of_sphereH1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.embeddedSphere_relativeH1_iso_int_of_openBicollar_of_sphereH1 ``Submission.DifferentialGeometry.Topology.SphereSeparation.embeddedSphere_relativeH1_iso_int_of_openBicollar_of_sphereH1

theorem embeddedSphere_relativeH1_iso_int_of_openBicollar
    {a : ℝ} (ha : 0 < a)
    (e : SphereTwo → EuclideanThree)
    (Φ : SphereTwo × AxialInterval a → EuclideanThree)
    (hΦ : _root_.Topology.IsOpenEmbedding Φ)
    (hzero : ∀ p, Φ (p, axialZero ha) = e p)
    (comparison : HomotopyEquiv
      (integerSingularChains (TopCat.of SphereTwo))
      sphereTwoCellularChainComplex) :
    Nonempty
      (relativeSingularHomologyOfSubspace (Set.range e)ᶜ 1 ≅
        ModuleCat.of ℤ ℤ) :=
  embeddedSphere_relativeH1_iso_int_of_openBicollar_of_sphereH1
    ha e Φ hΦ hzero
      (isZero_integerSingularHomology_sphereTwo_one_of_cellularComparison
        comparison)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.embeddedSphere_relativeH1_iso_int_of_openBicollar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.embeddedSphere_relativeH1_iso_int_of_openBicollar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.embeddedSphere_relativeH1_iso_int_of_openBicollar ``Submission.DifferentialGeometry.Topology.SphereSeparation.embeddedSphere_relativeH1_iso_int_of_openBicollar

theorem hasAlexanderDualityH0Certificate_of_openBicollar_of_sphereH1
    {a : ℝ} (ha : 0 < a)
    (e : SphereTwo → EuclideanThree)
    (Φ : SphereTwo × AxialInterval a → EuclideanThree)
    (hΦ : _root_.Topology.IsOpenEmbedding Φ)
    (hzero : ∀ p, Φ (p, axialZero ha) = e p)
    (hSphere : _root_.CategoryTheory.Limits.IsZero
      (integerSingularHomology (TopCat.of SphereTwo) 1)) :
    HasAlexanderDualityH0Certificate e :=
  hasAlexanderDualityH0Certificate_of_relativeH1 e
    (embeddedSphere_relativeH1_iso_int_of_openBicollar_of_sphereH1
      ha e Φ hΦ hzero hSphere)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.hasAlexanderDualityH0Certificate_of_openBicollar_of_sphereH1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.hasAlexanderDualityH0Certificate_of_openBicollar_of_sphereH1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.hasAlexanderDualityH0Certificate_of_openBicollar_of_sphereH1 ``Submission.DifferentialGeometry.Topology.SphereSeparation.hasAlexanderDualityH0Certificate_of_openBicollar_of_sphereH1

theorem hasAlexanderDualityH0Certificate_of_openBicollar
    {a : ℝ} (ha : 0 < a)
    (e : SphereTwo → EuclideanThree)
    (Φ : SphereTwo × AxialInterval a → EuclideanThree)
    (hΦ : _root_.Topology.IsOpenEmbedding Φ)
    (hzero : ∀ p, Φ (p, axialZero ha) = e p)
    (comparison : HomotopyEquiv
      (integerSingularChains (TopCat.of SphereTwo))
      sphereTwoCellularChainComplex) :
    HasAlexanderDualityH0Certificate e :=
  hasAlexanderDualityH0Certificate_of_openBicollar_of_sphereH1
    ha e Φ hΦ hzero
      (isZero_integerSingularHomology_sphereTwo_one_of_cellularComparison
        comparison)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.hasAlexanderDualityH0Certificate_of_openBicollar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.hasAlexanderDualityH0Certificate_of_openBicollar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.hasAlexanderDualityH0Certificate_of_openBicollar ``Submission.DifferentialGeometry.Topology.SphereSeparation.hasAlexanderDualityH0Certificate_of_openBicollar

end DifferentialGeometry.Topology.SphereSeparation
