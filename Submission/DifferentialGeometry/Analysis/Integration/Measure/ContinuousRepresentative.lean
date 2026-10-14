import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.ContinuousOn

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped _root_.Topology

namespace MeasureTheory
open _root_.MeasureTheory

open _root_.MeasureTheory in
theorem exists_continuousOn_ae_eq_of_isLindelof
    {X Y : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    [TopologicalSpace Y] [T2Space Y]
    (μ : _root_.MeasureTheory.Measure X) [μ.IsOpenPosMeasure] {Ω : Set X} {w : X → Y}
    (hΩ : IsLindelof Ω)
    (hloc : ∀ x ∈ Ω, ∃ (U : Set X) (f : X → Y),
      IsOpen U ∧ x ∈ U ∧ U ⊆ Ω ∧ ContinuousOn f U ∧ f =ᵐ[μ.restrict U] w) :
    ∃ v : X → Y, ContinuousOn v Ω ∧ v =ᵐ[μ.restrict Ω] w := by
  classical
  choose U f hU hxU hsub hcont hae using (fun x : Ω => hloc x x.property)
  let v : X → Y := fun x => if hx : x ∈ Ω then f ⟨x, hx⟩ x else w x
  have hoverlap (i j : Ω) : _root_.Set.EqOn (f i) (f j) (U i ∩ U j) := by
    apply μ.eqOn_open_of_ae_eq _ ((hU i).inter (hU j))
      ((hcont i).mono _root_.Set.inter_subset_left) ((hcont j).mono _root_.Set.inter_subset_right)
    have hi : f i =ᵐ[μ.restrict (U i ∩ U j)] w :=
      _root_.MeasureTheory.ae_restrict_of_ae_restrict_of_subset _root_.Set.inter_subset_left (hae i)
    have hj : f j =ᵐ[μ.restrict (U i ∩ U j)] w :=
      _root_.MeasureTheory.ae_restrict_of_ae_restrict_of_subset _root_.Set.inter_subset_right (hae j)
    exact hi.trans hj.symm
  have hvlocal (i : Ω) : _root_.Set.EqOn v (f i) (U i) := by
    intro x hx
    have hxΩ := hsub i hx
    dsimp only [v]
    rw [dif_pos hxΩ]
    exact hoverlap ⟨x, hxΩ⟩ i ⟨hxU ⟨x, hxΩ⟩, hx⟩
  have hvc : ContinuousOn v Ω := by
    apply continuousOn_of_locally_continuousOn
    intro x hx
    let i : Ω := ⟨x, hx⟩
    refine ⟨U i, hU i, hxU i, ?_⟩
    exact ((hcont i).congr (hvlocal i)).mono _root_.Set.inter_subset_right
  have hcover : (⋃ i : Ω, U i) = Ω := by
    apply Subset.antisymm
    · exact _root_.Set.iUnion_subset hsub
    · intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
  obtain ⟨T, hT, hTcover⟩ := hΩ.elim_countable_subcover U hU (by rw [hcover])
  have hTU : (⋃ i ∈ T, U i) = Ω := hTcover.antisymm'
    (_root_.Set.iUnion₂_subset fun i _ => hsub i)
  have hvae : v =ᵐ[μ.restrict (⋃ i ∈ T, U i)] w := by
    apply (_root_.MeasureTheory.ae_restrict_biUnion_iff U hT _).mpr
    intro i hi
    filter_upwards [hae i, _root_.MeasureTheory.ae_restrict_mem (hU i).measurableSet] with x hx hxU'
    exact (hvlocal i hxU').trans hx
  rw [hTU] at hvae
  exact ⟨v, hvc, hvae⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.exists_continuousOn_ae_eq_of_isLindelof then
    throwError "Refusing to shadow existing declaration MeasureTheory.exists_continuousOn_ae_eq_of_isLindelof"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.exists_continuousOn_ae_eq_of_isLindelof ``Submission.MeasureTheory.exists_continuousOn_ae_eq_of_isLindelof

open _root_.MeasureTheory in
theorem exists_continuousOn_ae_eq_of_locally_continuousOn_ae_eq
    {X Y : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    [TopologicalSpace Y] [T2Space Y]
    (μ : _root_.MeasureTheory.Measure X) [μ.IsOpenPosMeasure] {Ω : Set X} {w : X → Y}
    (hloc : ∀ x ∈ Ω, ∃ (U : Set X) (f : X → Y),
      IsOpen U ∧ x ∈ U ∧ U ⊆ Ω ∧ ContinuousOn f U ∧ f =ᵐ[μ.restrict U] w) :
    ∃ v : X → Y, ContinuousOn v Ω ∧ v =ᵐ[μ.restrict Ω] w :=
  exists_continuousOn_ae_eq_of_isLindelof μ (HereditarilyLindelofSpace.isLindelof Ω) hloc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.exists_continuousOn_ae_eq_of_locally_continuousOn_ae_eq then
    throwError "Refusing to shadow existing declaration MeasureTheory.exists_continuousOn_ae_eq_of_locally_continuousOn_ae_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.exists_continuousOn_ae_eq_of_locally_continuousOn_ae_eq ``Submission.MeasureTheory.exists_continuousOn_ae_eq_of_locally_continuousOn_ae_eq

theorem ContinuousOn.mapsTo_of_ae_mem_closed
    {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [TopologicalSpace Y] (μ : _root_.MeasureTheory.Measure X) [μ.IsOpenPosMeasure]
    {Ω : Set X} (hΩ : IsOpen Ω) {K : Set Y} (hK : IsClosed K) {f : X → Y}
    (hf : ContinuousOn f Ω) (hmem : ∀ᵐ x ∂μ.restrict Ω, f x ∈ K) : _root_.Set.MapsTo f Ω K := by
  have hopen : IsOpen (Ω ∩ f ⁻¹' Kᶜ) := hf.isOpen_inter_preimage hΩ hK.isOpen_compl
  have hzero : μ (Ω ∩ f ⁻¹' Kᶜ) = 0 := by
    have h := (_root_.MeasureTheory.ae_restrict_iff' hΩ.measurableSet).mp hmem
    rw [_root_.MeasureTheory.ae_iff] at h
    have heq : Ω ∩ f ⁻¹' Kᶜ = {x | ¬ (x ∈ Ω → f x ∈ K)} := by
      ext x
      simp only [_root_.Set.mem_inter_iff, _root_.Set.mem_preimage, _root_.Set.mem_compl_iff, _root_.Set.mem_ofPred_eq, Classical.not_imp]
    rw [heq]
    exact h
  have hempty := hopen.eq_empty_of_measure_zero hzero
  intro x hx
  by_contra hxK
  have : x ∈ Ω ∩ f ⁻¹' Kᶜ := ⟨hx, hxK⟩
  rw [hempty] at this
  exact this

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.MeasureTheory.ContinuousOn
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.ContinuousOn.mapsTo_of_ae_mem_closed then
    throwError "Refusing to shadow existing declaration MeasureTheory.ContinuousOn.mapsTo_of_ae_mem_closed"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.ContinuousOn.mapsTo_of_ae_mem_closed ``Submission.MeasureTheory.ContinuousOn.mapsTo_of_ae_mem_closed

end MeasureTheory
