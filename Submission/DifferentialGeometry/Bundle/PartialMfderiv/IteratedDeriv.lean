import Submission.DifferentialGeometry.Bundle.PartialMfderiv.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Comp

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

open _root_.Set
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contMDiffAt_deriv_snd {G : M × ℝ → F} {p : M × ℝ} {m n : ℕ∞ω}
    (hG : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) n G p) (hmn : m + 1 ≤ n) :
    ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) m
      (fun q : M × ℝ => deriv (fun s => G (q.1, s)) q.2) p := by
  have hs : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) n
      (fun q : ℝ × M => G (q.2, q.1)) (p.2, p.1) :=
    hG.comp (p.2, p.1) (contMDiffAt_snd.prodMk contMDiffAt_fst)
  have hd := DifferentialGeometry.timeDeriv_smoothAt hs hmn
  exact hd.comp p (contMDiffAt_snd.prodMk contMDiffAt_fst)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.contMDiffAt_deriv_snd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.contMDiffAt_deriv_snd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.contMDiffAt_deriv_snd ``Submission.DifferentialGeometry.Analysis.contMDiffAt_deriv_snd

theorem contMDiffAt_iteratedDeriv_snd_of_add_le {G : M × ℝ → F} {p : M × ℝ}
    {m n : ℕ∞ω} (hG : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) n G p)
    (j : ℕ) (hmn : m + j ≤ n) :
    ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) m
      (fun q : M × ℝ => iteratedDeriv j (fun s => G (q.1, s)) q.2) p := by
  induction j generalizing m with
  | zero =>
    exact hG.of_le (by simpa only [Nat.cast_zero, add_zero] using hmn)
  | succ j ih =>
    have hsum : (m + 1) + j ≤ n := by
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm (1 : ℕ∞ω) (j : ℕ∞ω)] using hmn
    simpa only [iteratedDeriv_succ] using contMDiffAt_deriv_snd (ih hsum) le_rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.contMDiffAt_iteratedDeriv_snd_of_add_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.contMDiffAt_iteratedDeriv_snd_of_add_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.contMDiffAt_iteratedDeriv_snd_of_add_le ``Submission.DifferentialGeometry.Analysis.contMDiffAt_iteratedDeriv_snd_of_add_le

theorem contMDiffAt_iteratedDeriv_snd {G : M × ℝ → F} {p : M × ℝ}
    (hG : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) ∞ G p) (j : ℕ) :
    ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) ∞
      (fun q : M × ℝ => iteratedDeriv j (fun s => G (q.1, s)) q.2) p := by
  exact contMDiffAt_iteratedDeriv_snd_of_add_le hG j
    (WithTop.coe_le_coe.mpr le_top)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.contMDiffAt_iteratedDeriv_snd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.contMDiffAt_iteratedDeriv_snd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.contMDiffAt_iteratedDeriv_snd ``Submission.DifferentialGeometry.Analysis.contMDiffAt_iteratedDeriv_snd

theorem contMDiffOn_iteratedDeriv_snd {G : M × ℝ → F} {U : Set (M × ℝ)}
    (hU : IsOpen U) (hG : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) ∞ G U) (j : ℕ) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) ∞
      (fun q : M × ℝ => iteratedDeriv j (fun s => G (q.1, s)) q.2) U := by
  intro p hp
  exact (contMDiffAt_iteratedDeriv_snd (hG.contMDiffAt (hU.mem_nhds hp)) j).contMDiffWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.contMDiffOn_iteratedDeriv_snd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.contMDiffOn_iteratedDeriv_snd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.contMDiffOn_iteratedDeriv_snd ``Submission.DifferentialGeometry.Analysis.contMDiffOn_iteratedDeriv_snd

theorem continuousOn_iteratedDeriv_snd_of_contMDiffOn {G : M × ℝ → F} {U : Set (M × ℝ)}
    (hU : IsOpen U) (hG : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) ∞ G U) (j : ℕ) :
    ContinuousOn (fun q : M × ℝ => iteratedDeriv j (fun s => G (q.1, s)) q.2) U :=
  (contMDiffOn_iteratedDeriv_snd hU hG j).continuousOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.continuousOn_iteratedDeriv_snd_of_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.continuousOn_iteratedDeriv_snd_of_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.continuousOn_iteratedDeriv_snd_of_contMDiffOn ``Submission.DifferentialGeometry.Analysis.continuousOn_iteratedDeriv_snd_of_contMDiffOn

end DifferentialGeometry.Analysis

end

section

open _root_.Set
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Type*} [TopologicalSpace K]

theorem continuousOn_iteratedDeriv_parameter_comp
    {G : M × ℝ → F} {U : Set M} {J : Set ℝ}
    (hU : IsOpen U) (hJ : IsOpen J)
    (hG : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) ∞ G (U ×ˢ J))
    {v : K → M} (hv : Continuous v) (hvU : ∀ k, v k ∈ U)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) {s : Set ℝ} (hs : _root_.Set.MapsTo β s J) (j : ℕ) :
    ContinuousOn (fun q : K × ℝ =>
      iteratedDeriv j (fun t => G (v q.1, β t)) q.2) (_root_.Set.univ ×ˢ s) := by
  have hsm : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) ∞
      (fun p : M × ℝ => G (p.1, β p.2)) (U ×ˢ (β ⁻¹' J)) := by
    apply hG.comp
      (contMDiff_fst.prodMk (hβ.contMDiff.comp contMDiff_snd)).contMDiffOn
    intro p hp
    exact ⟨hp.1, hp.2⟩
  have hj := continuousOn_iteratedDeriv_snd_of_contMDiffOn
    (hU.prod (hJ.preimage hβ.continuous)) hsm j
  exact hj.comp (hv.comp continuous_fst |>.prodMk continuous_snd).continuousOn
    (fun p hp => ⟨hvU p.1, hs hp.2⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.continuousOn_iteratedDeriv_parameter_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.continuousOn_iteratedDeriv_parameter_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.continuousOn_iteratedDeriv_parameter_comp ``Submission.DifferentialGeometry.Analysis.continuousOn_iteratedDeriv_parameter_comp

end DifferentialGeometry.Analysis

end
