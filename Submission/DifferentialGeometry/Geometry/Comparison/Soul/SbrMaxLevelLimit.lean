import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Filter _root_.Set
open scoped _root_.Topology

namespace DifferentialGeometry.Geometry.Topology

variable {M : Type*} [MetricSpace M]

theorem exists_level_left_limit_of_dist_antitone
    {C : Set M} (hC : IsCompact C) (F : M → ℝ) (hF : ContinuousOn F C)
    (eta : ℝ → M) {a m : ℝ} (ham : a < m)
    (hetaC : ∀ s ∈ _root_.Set.Ico a m, eta s ∈ C)
    (hlevel : ∀ s ∈ _root_.Set.Ico a m, F (eta s) = s)
    (hdist : ∀ q ∈ C, F q = m → AntitoneOn (fun s => _root_.Dist.dist (eta s) q) (_root_.Set.Ico a m)) :
    ∃ q ∈ C, F q = m ∧ _root_.Filter.Tendsto eta (𝓝[<] m) (𝓝 q) := by
  obtain ⟨u, _hmono, hu, hulim⟩ := exists_seq_strictMono_tendsto' ham
  have huIco (n : ℕ) : u n ∈ _root_.Set.Ico a m := ⟨(hu n).1.le, (hu n).2⟩
  obtain ⟨q, hqC, phi, hphi, hq⟩ :=
    hC.tendsto_subseq (fun n => hetaC (u n) (huIco n))
  have hqWithin : _root_.Filter.Tendsto (fun n => eta (u (phi n))) _root_.Filter.atTop (𝓝[C] q) :=
    tendsto_nhdsWithin_iff.mpr ⟨hq,
      Eventually.of_forall (fun n => hetaC (u (phi n)) (huIco (phi n)))⟩
  have hFq : _root_.Filter.Tendsto (fun n => F (eta (u (phi n)))) _root_.Filter.atTop (𝓝 (F q)) :=
    Filter.Tendsto.comp (hF q hqC) hqWithin
  have hFq' : _root_.Filter.Tendsto (u ∘ phi) _root_.Filter.atTop (𝓝 (F q)) := by
    have heq : (fun n => F (eta (u (phi n)))) = u ∘ phi := by
      funext n
      exact hlevel (u (phi n)) (huIco (phi n))
    rwa [heq] at hFq
  have hqm : F q = m := tendsto_nhds_unique hFq' (hulim.comp hphi.tendsto_atTop)
  refine ⟨q, hqC, hqm, ?_⟩
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  have hnear : ∀ᶠ n in _root_.Filter.atTop, _root_.Dist.dist (eta (u (phi n))) q < eps :=
    Metric.tendsto_nhds.mp hq eps heps
  obtain ⟨n, hn⟩ := hnear.exists
  filter_upwards [Ioo_mem_nhdsLT (hu (phi n)).2] with s hs
  have hsIco : s ∈ _root_.Set.Ico a m :=
    ⟨(hu (phi n)).1.le.trans hs.1.le, hs.2⟩
  exact ((hdist q hqC hqm) (huIco (phi n)) hsIco hs.1.le).trans_lt hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.exists_level_left_limit_of_dist_antitone then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.exists_level_left_limit_of_dist_antitone"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.exists_level_left_limit_of_dist_antitone ``Submission.DifferentialGeometry.Geometry.Topology.exists_level_left_limit_of_dist_antitone

theorem exists_continuous_level_extension_of_dist_antitone
    {C : Set M} (hC : IsCompact C) (F : M → ℝ) (hF : ContinuousOn F C)
    (eta : ℝ → M) {a m : ℝ} (ham : a < m)
    (heta : ContinuousOn eta (_root_.Set.Ico a m))
    (hetaC : ∀ s ∈ _root_.Set.Ico a m, eta s ∈ C)
    (hlevel : ∀ s ∈ _root_.Set.Ico a m, F (eta s) = s)
    (hdist : ∀ q ∈ C, F q = m → AntitoneOn (fun s => _root_.Dist.dist (eta s) q) (_root_.Set.Ico a m)) :
    ∃ q ∈ C, F q = m ∧
      let etaBar := Function.update eta m q
      ContinuousOn etaBar (_root_.Set.Icc a m) ∧
      _root_.Set.EqOn etaBar eta (_root_.Set.Ico a m) ∧ etaBar m = q ∧
      ∀ s ∈ _root_.Set.Icc a m, etaBar s ∈ C ∧ F (etaBar s) = s := by
  obtain ⟨q, hqC, hqm, hlim⟩ :=
    exists_level_left_limit_of_dist_antitone hC F hF eta ham hetaC hlevel hdist
  have hcont : ContinuousOn (Function.update eta m q) (_root_.Set.Icc a m) := by
    apply continuousOn_update_iff.mpr
    constructor
    · simpa only [_root_.Set.Icc_sdiff_right] using heta
    · intro _hm
      rw [_root_.Set.Icc_sdiff_right]
      exact hlim.mono_left (nhdsWithin_mono m _root_.Set.Ico_subset_Iio_self)
  refine ⟨q, hqC, hqm, hcont, ?_, Function.update_self m q eta, ?_⟩
  · intro s hs
    exact Function.update_of_ne hs.2.ne q eta
  · intro s hs
    rcases eq_or_lt_of_le hs.2 with rfl | hsm
    · simpa only [Function.update_self] using And.intro hqC hqm
    · rw [Function.update_of_ne hsm.ne]
      exact ⟨hetaC s ⟨hs.1, hsm⟩, hlevel s ⟨hs.1, hsm⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.exists_continuous_level_extension_of_dist_antitone then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.exists_continuous_level_extension_of_dist_antitone"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.exists_continuous_level_extension_of_dist_antitone ``Submission.DifferentialGeometry.Geometry.Topology.exists_continuous_level_extension_of_dist_antitone

end DifferentialGeometry.Geometry.Topology
