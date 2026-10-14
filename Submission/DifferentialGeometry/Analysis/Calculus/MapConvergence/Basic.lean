import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.MetricSpace.Pseudo.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open _root_.Filter _root_.Topology

section MapConvergence

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def mapDerivNorm (r : ℕ) (Φk Φinf : E → F) (x : E) : ℝ :=
  ‖iteratedFDeriv ℝ r (fun y => Φk y - Φinf y) x‖

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.mapDerivNorm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.mapDerivNorm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.mapDerivNorm ``Submission.DifferentialGeometry.CheegerGromovCompactness.mapDerivNorm

theorem mapDerivNorm_nonneg (r : ℕ) (Φk Φinf : E → F) (x : E) :
    0 ≤ mapDerivNorm r Φk Φinf x :=
  norm_nonneg _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.mapDerivNorm_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.mapDerivNorm_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.mapDerivNorm_nonneg ``Submission.DifferentialGeometry.CheegerGromovCompactness.mapDerivNorm_nonneg

def MapCPConvergenceOn (K : Set E) (p : ℕ) (Φ : ℕ → E → F) (Φinf : E → F) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
    ∀ r : ℕ, r ≤ p → ∀ x ∈ K, mapDerivNorm r (Φ k) Φinf x ≤ ε

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MapCPConvergenceOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MapCPConvergenceOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MapCPConvergenceOn ``Submission.DifferentialGeometry.CheegerGromovCompactness.MapCPConvergenceOn

def MapCInfConvergenceOnCompacts (U : Set E) (Φ : ℕ → E → F) (Φinf : E → F) : Prop :=
  ∀ K : Set E, IsCompact K → K ⊆ U → ∀ p : ℕ, MapCPConvergenceOn K p Φ Φinf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MapCInfConvergenceOnCompacts then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MapCInfConvergenceOnCompacts"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MapCInfConvergenceOnCompacts ``Submission.DifferentialGeometry.CheegerGromovCompactness.MapCInfConvergenceOnCompacts

theorem MapCPConvergenceOn.mono_order {K : Set E} {p p' : ℕ} (hp : p' ≤ p)
    {Φ : ℕ → E → F} {Φinf : E → F} (h : MapCPConvergenceOn K p Φ Φinf) :
    MapCPConvergenceOn K p' Φ Φinf := by
  intro ε hε
  obtain ⟨k0, hk0⟩ := h ε hε
  exact ⟨k0, fun k hk r hr x hx => hk0 k hk r (hr.trans hp) x hx⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.CheegerGromovCompactness.MapCPConvergenceOn
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MapCPConvergenceOn.mono_order then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MapCPConvergenceOn.mono_order"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MapCPConvergenceOn.mono_order ``Submission.DifferentialGeometry.CheegerGromovCompactness.MapCPConvergenceOn.mono_order


theorem MapCPConvergenceOn.mono_set {K K' : Set E} (hK : K' ⊆ K) {p : ℕ}
    {Φ : ℕ → E → F} {Φinf : E → F} (h : MapCPConvergenceOn K p Φ Φinf) :
    MapCPConvergenceOn K' p Φ Φinf := by
  intro ε hε
  obtain ⟨k0, hk0⟩ := h ε hε
  exact ⟨k0, fun k hk r hr x hx => hk0 k hk r hr x (hK hx)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MapCPConvergenceOn.mono_set then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MapCPConvergenceOn.mono_set"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MapCPConvergenceOn.mono_set ``Submission.DifferentialGeometry.CheegerGromovCompactness.MapCPConvergenceOn.mono_set

theorem MapCInfConvergenceOnCompacts.cPConvergenceOn {U : Set E} {Φ : ℕ → E → F} {Φinf : E → F}
    (h : MapCInfConvergenceOnCompacts U Φ Φinf) {K : Set E} (hK : IsCompact K)
    (hKU : K ⊆ U) (p : ℕ) : MapCPConvergenceOn K p Φ Φinf :=
  h K hK hKU p

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.CheegerGromovCompactness.MapCInfConvergenceOnCompacts
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MapCInfConvergenceOnCompacts.cPConvergenceOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MapCInfConvergenceOnCompacts.cPConvergenceOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MapCInfConvergenceOnCompacts.cPConvergenceOn ``Submission.DifferentialGeometry.CheegerGromovCompactness.MapCInfConvergenceOnCompacts.cPConvergenceOn


theorem MapCPConvergenceOn.comp_subseq {K : Set E} {p : ℕ} {Φ : ℕ → E → F} {Φinf : E → F}
    (h : MapCPConvergenceOn K p Φ Φinf) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    MapCPConvergenceOn K p (fun k => Φ (φ k)) Φinf := by
  intro ε hε
  obtain ⟨k0, hk0⟩ := h ε hε
  exact ⟨k0, fun k hk r hr x hx => hk0 (φ k) (le_trans hk (hφ.id_le k)) r hr x hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MapCPConvergenceOn.comp_subseq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MapCPConvergenceOn.comp_subseq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MapCPConvergenceOn.comp_subseq ``Submission.DifferentialGeometry.CheegerGromovCompactness.MapCPConvergenceOn.comp_subseq


theorem MapCInfConvergenceOnCompacts.comp_subseq {U : Set E} {Φ : ℕ → E → F} {Φinf : E → F}
    (h : MapCInfConvergenceOnCompacts U Φ Φinf) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    MapCInfConvergenceOnCompacts U (fun k => Φ (φ k)) Φinf :=
  fun K hK hKU p => (h K hK hKU p).comp_subseq hφ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MapCInfConvergenceOnCompacts.comp_subseq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MapCInfConvergenceOnCompacts.comp_subseq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MapCInfConvergenceOnCompacts.comp_subseq ``Submission.DifferentialGeometry.CheegerGromovCompactness.MapCInfConvergenceOnCompacts.comp_subseq

theorem tendstoUniformlyOn_of_cPConvergence {K : Set E} {Φ : ℕ → E → F} {Φinf : E → F}
    (h : MapCPConvergenceOn K 0 Φ Φinf) : TendstoUniformlyOn Φ Φinf _root_.Filter.atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨k0, hk0⟩ := h (ε / 2) (by positivity)
  rw [_root_.Filter.eventually_atTop]
  refine ⟨k0, fun k hk x hx => ?_⟩
  have hb := hk0 k hk 0 le_rfl x hx
  rw [mapDerivNorm, norm_iteratedFDeriv_zero] at hb
  rw [dist_eq_norm, norm_sub_rev]
  exact lt_of_le_of_lt hb (by linarith)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.tendstoUniformlyOn_of_cPConvergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.tendstoUniformlyOn_of_cPConvergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.tendstoUniformlyOn_of_cPConvergence ``Submission.DifferentialGeometry.CheegerGromovCompactness.tendstoUniformlyOn_of_cPConvergence

theorem tendsto_of_cInf {U : Set E} {Φ : ℕ → E → F} {Φinf : E → F}
    (h : MapCInfConvergenceOnCompacts U Φ Φinf) {x : E} (hx : x ∈ U) :
    Tendsto (fun k => Φ k x) _root_.Filter.atTop (𝓝 (Φinf x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k0, hk0⟩ :=
    h {x} isCompact_singleton (Set.singleton_subset_iff.mpr hx) 0 (ε / 2) (by positivity)
  refine ⟨k0, fun k hk => ?_⟩
  have hb := hk0 k hk 0 le_rfl x rfl
  rw [mapDerivNorm, norm_iteratedFDeriv_zero] at hb
  rw [dist_eq_norm]
  exact lt_of_le_of_lt hb (by linarith)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.tendsto_of_cInf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.tendsto_of_cInf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.tendsto_of_cInf ``Submission.DifferentialGeometry.CheegerGromovCompactness.tendsto_of_cInf

theorem mapCPConvergenceOn_of_tendstoUniformly {K : Set E} {p : ℕ}
    {Φ : ℕ → E → F} {Φinf : E → F}
    (hΦ : ∀ k, ContDiff ℝ (p : ℕ∞) (Φ k)) (hΦinf : ContDiff ℝ (p : ℕ∞) Φinf)
    (htu : ∀ r : ℕ, r ≤ p →
      TendstoUniformlyOn (fun k x => iteratedFDeriv ℝ r (Φ k) x)
        (fun x => iteratedFDeriv ℝ r Φinf x) _root_.Filter.atTop K) :
    MapCPConvergenceOn K p Φ Φinf := by
  intro ε hε
  have key : ∀ r : ℕ, r ≤ p →
      ∀ᶠ k in _root_.Filter.atTop, ∀ x ∈ K, mapDerivNorm r (Φ k) Φinf x ≤ ε := by
    intro r hr
    have h := (Metric.tendstoUniformlyOn_iff.mp (htu r hr)) ε hε
    filter_upwards [h] with k hk x hx
    have hsub : iteratedFDeriv ℝ r (fun y => Φ k y - Φinf y) x
        = iteratedFDeriv ℝ r (Φ k) x - iteratedFDeriv ℝ r Φinf x :=
      iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := r) (x := x)
        ((hΦ k).contDiffAt.of_le (by exact_mod_cast hr))
        (hΦinf.contDiffAt.of_le (by exact_mod_cast hr))
    have hdist := hk x hx
    rw [dist_eq_norm, ← norm_sub_rev] at hdist
    rw [mapDerivNorm, hsub]
    exact hdist.le
  have hfin : ∀ᶠ k in _root_.Filter.atTop, ∀ r ∈ Set.Iic p, ∀ x ∈ K,
      mapDerivNorm r (Φ k) Φinf x ≤ ε :=
    (Set.finite_Iic p).eventually_all.2 (fun r hr => key r (Set.mem_Iic.mp hr))
  obtain ⟨k0, hk0⟩ := eventually_atTop.mp hfin
  exact ⟨k0, fun k hk r hr x hx => hk0 k hk r (Set.mem_Iic.mpr hr) x hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.mapCPConvergenceOn_of_tendstoUniformly then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.mapCPConvergenceOn_of_tendstoUniformly"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.mapCPConvergenceOn_of_tendstoUniformly ``Submission.DifferentialGeometry.CheegerGromovCompactness.mapCPConvergenceOn_of_tendstoUniformly

end MapConvergence

end CheegerGromovCompactness
end DifferentialGeometry
