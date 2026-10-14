import Submission.DifferentialGeometry.Topology.Morse.RelativePerturbationManifold

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Filter _root_.Function
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Morse
variable {M : Type*} [TopologicalSpace M] {n : ℕ}


theorem continuous_joint_finitePerturbation {f : M → ℝ} {φ : Fin n → M → ℝ}
    (hf : Continuous f) (hφ : ∀ i, Continuous (φ i)) :
    Continuous (fun q : (Fin n → ℝ) × M => finitePerturbation f φ q.1 q.2) := by
  apply (hf.comp continuous_snd).add
  exact continuous_finsetSum _ fun i _ =>
    ((continuous_apply i).comp continuous_fst).mul ((hφ i).comp continuous_snd)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.continuous_joint_finitePerturbation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.continuous_joint_finitePerturbation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.continuous_joint_finitePerturbation ``Submission.DifferentialGeometry.Morse.continuous_joint_finitePerturbation


theorem exists_pos_radius_finitePerturbation {f : M → ℝ} {φ : Fin n → M → ℝ} {S : Set M}
    (hf : Continuous f) (hφ : ∀ i, Continuous (φ i))
    (hc : ∀ i, HasCompactSupport (φ i)) (hs : ∀ i, tsupport (φ i) ⊆ S)
    (hpos : ∀ x ∈ S, 0 < f x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p : Fin n → ℝ, ‖p‖ < ε → ∀ x ∈ S,
      0 < finitePerturbation f φ p x := by
  let C : Set M := ⋃ i, tsupport (φ i)
  have hC : IsCompact C := isCompact_iUnion hc
  have hCS : C ⊆ S := _root_.Set.iUnion_subset hs
  have hJ := continuous_joint_finitePerturbation hf hφ
  have hnear : ∀ᶠ p : Fin n → ℝ in 𝓝 0, ∀ x ∈ C, 0 < finitePerturbation f φ p x := by
    apply hC.eventually_forall_of_forall_eventually
    intro x hx
    apply (isOpen_lt continuous_const hJ).mem_nhds
    change 0 < finitePerturbation f φ 0 x
    rw [finitePerturbation_zero]
    exact hpos x (hCS hx)
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨ε,hε,fun p hp x hx => ?_⟩
  by_cases hxC : x ∈ C
  · exact hball (show p ∈ Metric.ball 0 ε by simpa only [Metric.mem_ball,dist_zero_right] using hp) x hxC
  · have hz : ∀ i, φ i x = 0 := fun i => image_eq_zero_of_notMem_tsupport
      (fun hi => hxC (mem_iUnion.mpr ⟨i,hi⟩))
    simpa [finitePerturbation,hz] using hpos x hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.exists_pos_radius_finitePerturbation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.exists_pos_radius_finitePerturbation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.exists_pos_radius_finitePerturbation ``Submission.DifferentialGeometry.Morse.exists_pos_radius_finitePerturbation

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] [ChartedSpace H M] {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M] [T2Space M]


theorem exists_positive_relative_nondegenerate_perturbation {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {K U S : Set M}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (hKI : ∀ x ∈ K, I.IsInteriorPoint x)
    (hUS : U ⊆ S) (hpos : ∀ x ∈ S, 0 < f x) :
    ∃ g : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ g ∧
      (∃ N : Set M, IsOpen N ∧ Uᶜ ⊆ N ∧ _root_.Set.EqOn g f N) ∧
      (∀ x ∈ S, 0 < g x) ∧ ∀ x ∈ K, mfderiv I 𝓘(ℝ, ℝ) g x = 0 →
        Bijective (fderiv ℝ (fderiv ℝ (fun z => g ((extChartAt I x).symm z))) (extChartAt I x x)) := by
  obtain ⟨n,φ,hφ,hfix,hsmall⟩ :=
    exists_arbitrarily_small_relative_nondegenerate_manifold_finitePerturbation hf hK hU hKU hKI
  obtain ⟨ε,hε,hposε⟩ := exists_pos_radius_finitePerturbation hf.continuous
    (fun i => (hφ i).1.continuous) (fun i => (hφ i).2.1) (fun i => (hφ i).2.2.trans hUS) hpos
  obtain ⟨p,hp,hcrit⟩ := hsmall ε hε
  obtain ⟨N,hN,hUN,heq⟩ := hfix
  exact ⟨finitePerturbation f φ p,contMDiff_finitePerturbation hf (fun i => (hφ i).1) p,
    ⟨N,hN,hUN,heq p⟩,hposε p hp,hcrit⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.exists_positive_relative_nondegenerate_perturbation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.exists_positive_relative_nondegenerate_perturbation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.exists_positive_relative_nondegenerate_perturbation ``Submission.DifferentialGeometry.Morse.exists_positive_relative_nondegenerate_perturbation

end DifferentialGeometry.Morse
