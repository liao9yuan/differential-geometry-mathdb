/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ConeBase

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem convex_snd_eq_zero : Convex ℝ {q : E × ℝ | q.2 = 0} := by
  intro a ha b hb s t hs ht hst
  have ha' : a.2 = 0 := ha
  have hb' : b.2 = 0 := hb
  change (s • a + t • b).2 = 0
  simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, ha', hb', _root_.MulZeroClass.mul_zero, add_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.convex_snd_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.convex_snd_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.convex_snd_eq_zero ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.convex_snd_eq_zero

theorem snd_eq_zero_of_mem_space {L : Geometry.SimplicialComplex ℝ (E × ℝ)}
    (hverts : ∀ σ ∈ L.faces, ∀ v ∈ σ, (v : E × ℝ).2 = 0) {q : E × ℝ} (hq : q ∈ L.space) :
    q.2 = 0 := by
  obtain ⟨σ, hσ, hqσ⟩ := L.mem_space_iff.mp hq
  exact convexHull_min (fun v hv => hverts σ hσ v (Finset.mem_coe.mp hv)) convex_snd_eq_zero hqσ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.snd_eq_zero_of_mem_space then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.snd_eq_zero_of_mem_space"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.snd_eq_zero_of_mem_space ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.snd_eq_zero_of_mem_space

theorem isConeBase_of_snd_eq_zero (L : Geometry.SimplicialComplex ℝ (E × ℝ))
    (hL : ∀ q ∈ L.space, (q : E × ℝ).2 = 0) (x₀ : E) :
    IsConeBase ((x₀, 1) : E × ℝ) L where
  notMem_space := by
    intro hp
    have := hL _ hp
    norm_num at this
  indep := by
    classical
    intro σ hσ
    have hpσ : ((x₀, 1) : E × ℝ) ∉ σ := by
      intro hp
      have hmem : ((x₀, 1) : E × ℝ) ∈ L.space :=
        L.convexHull_subset_space hσ (subset_convexHull ℝ _ (Finset.mem_coe.mpr hp))
      have := hL _ hmem
      norm_num at this
    rw [← Finset.coe_insert]
    refine (affineIndependent_insert_iff hpσ (L.indep hσ)).mpr ?_
    rintro ⟨c, hc₁, hcp⟩
    have hzero : ∀ v ∈ σ, (c v • v : E × ℝ).2 = 0 := by
      intro v hv
      have hvmem : (v : E × ℝ) ∈ L.space :=
        L.convexHull_subset_space hσ (subset_convexHull ℝ _ (Finset.mem_coe.mpr hv))
      simp only [Prod.smul_snd, smul_eq_mul, hL _ hvmem, _root_.MulZeroClass.mul_zero]
    have hsum : (∑ v ∈ σ, c v • (v : E × ℝ)).2 = 0 := by
      rw [Prod.snd_sum]
      exact Finset.sum_eq_zero hzero
    rw [hcp] at hsum
    norm_num at hsum
  radial := by
    intro x hx y hy t ht hxy
    have hx' : x.2 = 0 := hL _ hx
    have hy' : y.2 = 0 := hL _ hy
    have hsnd : y.2 = 1 + t * (x.2 - 1) := by
      rw [hxy]
      simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]
    rw [hx', hy'] at hsnd
    have ht1 : t = 1 := by linarith
    rw [hxy, ht1, one_smul, add_sub_cancel]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isConeBase_of_snd_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isConeBase_of_snd_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isConeBase_of_snd_eq_zero ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isConeBase_of_snd_eq_zero

end DifferentialGeometry.Topology.PiecewiseLinear
