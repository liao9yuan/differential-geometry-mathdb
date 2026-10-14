import Submission.DifferentialGeometry.Analysis.Calculus.MapConvergence.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.OpenPartialHomeomorph.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section
open _root_.Set _root_.Filter _root_.Topology
namespace DifferentialGeometry.CheegerGromovCompactness

variable {E Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [LocallyCompactSpace E] [TopologicalSpace Q]

theorem tendsto_source_coordinates_of_tendsto
    (U : TopologicalSpace.Opens E) (e : OpenPartialHomeomorph U Q)
    (he : e.source = _root_.Set.univ) (V : TopologicalSpace.Opens Q)
    (A : ℕ → E → E)
    (hA : MapCInfConvergenceOnCompacts (Subtype.val '' (e ⁻¹' (V : Set Q))) A id)
    {z : U} (hzV : e z ∈ V) {q : ℕ → Q}
    (hq : _root_.Filter.Tendsto q _root_.Filter.atTop (nhds (e z)))
    (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    Tendsto (fun n => A (φ n) ((e.symm (q n) : U) : E)) _root_.Filter.atTop (nhds (z : E)) := by
  have hz : z ∈ e.source := he.symm ▸ _root_.Set.mem_univ z
  have hinv : _root_.Filter.Tendsto (fun n => e.symm (q n)) _root_.Filter.atTop (nhds z) := by
    have h := (e.symm.continuousAt (e.map_source hz)).tendsto.comp hq
    rwa [e.left_inv hz] at h
  have hc := continuous_subtype_val.tendsto z |>.comp hinv
  have hopen : IsOpen (Subtype.val '' (e ⁻¹' (V : Set Q))) := by
    apply U.isOpen.isOpenMap_subtype_val
    apply V.isOpen.preimage
    exact continuousOn_univ.mp (he ▸ e.continuousOn)
  have hzDom : (z : E) ∈ Subtype.val '' (e ⁻¹' (V : Set Q)) := ⟨z, hzV, rfl⟩
  obtain ⟨K, hK, hzK, hKDom⟩ := exists_compact_subset hopen hzDom
  have hcK : _root_.Filter.Tendsto (fun n => ((e.symm (q n) : U) : E)) _root_.Filter.atTop (nhdsWithin (z : E) K) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hc
      (hc.eventually (mem_interior_iff_mem_nhds.mp hzK))
  exact (tendstoUniformlyOn_of_cPConvergence ((hA.comp_subseq hφ) K hK hKDom 0)).tendsto_comp
    continuousWithinAt_id hcK

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.tendsto_source_coordinates_of_tendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.tendsto_source_coordinates_of_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.tendsto_source_coordinates_of_tendsto ``Submission.DifferentialGeometry.CheegerGromovCompactness.tendsto_source_coordinates_of_tendsto

theorem tendsto_source_chart_inverse_of_chart_convergence
    (U : TopologicalSpace.Opens E) (e : OpenPartialHomeomorph U Q)
    (he : e.source = _root_.Set.univ) (V : TopologicalSpace.Opens Q)
    {M : ℕ → Type*} [∀ n, TopologicalSpace (M n)]
    (c : ∀ n, OpenPartialHomeomorph E (M n)) (F : ∀ n, Q → M n)
    (A : ℕ → E → E)
    (hA : MapCInfConvergenceOnCompacts (Subtype.val '' (e ⁻¹' (V : Set Q))) A id)
    (hcoords : ∀ n (z : U), A n z = (c n).symm (F n (e z)))
    (himage : ∀ L : Set E, IsCompact L → L ⊆ Subtype.val '' (e ⁻¹' (V : Set Q)) →
      ∀ᶠ n in _root_.Filter.atTop, ∀ z : U, (z : E) ∈ L → F n (e z) ∈ (c n).target)
    {z : U} (hzV : e z ∈ V) {q : ℕ → Q}
    (hq : _root_.Filter.Tendsto q _root_.Filter.atTop (nhds (e z)))
    (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    _root_.Filter.Tendsto (fun n => (c (φ n)).symm (F (φ n) (q n))) _root_.Filter.atTop (nhds (z : E)) ∧
      ∀ᶠ n in _root_.Filter.atTop, F (φ n) (q n) ∈ (c (φ n)).target := by
  have hz : z ∈ e.source := he.symm ▸ _root_.Set.mem_univ z
  have hqt := hq.eventually (e.open_target.mem_nhds (e.map_source hz))
  have hcinv := tendsto_source_coordinates_of_tendsto U e he V A hA hzV hq φ hφ
  have hevent : (fun n => A (φ n) ((e.symm (q n) : U) : E)) =ᶠ[_root_.Filter.atTop]
      (fun n => (c (φ n)).symm (F (φ n) (q n))) := by
    filter_upwards [hqt] with n hn
    rw [hcoords, e.right_inv hn]
  refine ⟨hcinv.congr' hevent, ?_⟩
  have hinv : _root_.Filter.Tendsto (fun n => e.symm (q n)) _root_.Filter.atTop (nhds z) := by
    have h := (e.symm.continuousAt (e.map_source hz)).tendsto.comp hq
    rwa [e.left_inv hz] at h
  have hc := continuous_subtype_val.tendsto z |>.comp hinv
  have hopen : IsOpen (Subtype.val '' (e ⁻¹' (V : Set Q))) :=
    U.isOpen.isOpenMap_subtype_val _ (V.isOpen.preimage
      (continuousOn_univ.mp (he ▸ e.continuousOn)))
  obtain ⟨K, hK, hzK, hKDom⟩ := exists_compact_subset hopen ⟨z, hzV, rfl⟩
  have hKtail := hc.eventually (mem_interior_iff_mem_nhds.mp hzK)
  have htarget := hφ.tendsto_atTop.eventually (himage K hK hKDom)
  filter_upwards [hqt, hKtail, htarget] with n hn hkn htn
  have ht := htn (e.symm (q n)) hkn
  rwa [e.right_inv hn] at ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.tendsto_source_chart_inverse_of_chart_convergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.tendsto_source_chart_inverse_of_chart_convergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.tendsto_source_chart_inverse_of_chart_convergence ``Submission.DifferentialGeometry.CheegerGromovCompactness.tendsto_source_chart_inverse_of_chart_convergence

end DifferentialGeometry.CheegerGromovCompactness

end

end
