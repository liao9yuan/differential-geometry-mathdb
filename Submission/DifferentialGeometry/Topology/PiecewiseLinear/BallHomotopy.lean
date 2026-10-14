/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLBallSphere
import Mathlib.Analysis.Convex.Contractible

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLBall.contractibleSpace {n : ℕ} {D : Set E} (hD : IsPLBall n D) :
    ContractibleSpace D := by
  obtain ⟨r, hr⟩ := hD
  let _ : ContractibleSpace (stdSimplex ℝ (Fin (n + 1))) :=
    (convex_stdSimplex ℝ (Fin (n + 1))).contractibleSpace
      ⟨_, single_mem_stdSimplex ℝ (0 : Fin (n + 1))⟩
  exact hr.homeomorph.symm.contractibleSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.contractibleSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.contractibleSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.contractibleSpace ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.contractibleSpace

theorem IsPLBall.nullhomotopic_inclusion {n : ℕ} {D A S : Set E} (hD : IsPLBall n D)
    (hAD : A ⊆ D) (hDS : D ⊆ S) :
    (⟨Set.inclusion (hAD.trans hDS), continuous_inclusion _⟩ : C(A, S)).Nullhomotopic := by
  let _ := hD.contractibleSpace
  let i : C(A, D) := ⟨Set.inclusion hAD, continuous_inclusion hAD⟩
  let j : C(D, S) := ⟨Set.inclusion hDS, continuous_inclusion hDS⟩
  exact ((id_nullhomotopic D).comp_left i).comp_right j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.nullhomotopic_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.nullhomotopic_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.nullhomotopic_inclusion ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.nullhomotopic_inclusion

theorem IsPLBall.nullhomotopic_inclusion_of_cylinder {n : ℕ} {D J S : Set E}
    (hD : IsPLBall n D) (hDS : D ⊆ S) (hJS : J ⊆ S) {ρ : E × ℝ → E}
    (hρ : ContinuousOn ρ (J ×ˢ _root_.Set.Icc (0 : ℝ) 1))
    (hρS : _root_.Set.MapsTo ρ (J ×ˢ _root_.Set.Icc (0 : ℝ) 1) S)
    (hzero : ∀ x ∈ J, ρ (x, 0) = x) (hone : ∀ x ∈ J, ρ (x, 1) ∈ D) :
    (⟨Set.inclusion hJS, continuous_inclusion hJS⟩ : C(J, S)).Nullhomotopic := by
  let _ := hD.contractibleSpace
  let i : C(J, S) := ⟨Set.inclusion hJS, continuous_inclusion hJS⟩
  let j : C(D, S) := ⟨Set.inclusion hDS, continuous_inclusion hDS⟩
  let g : C(J, D) :=
    ⟨fun x => ⟨ρ (x, 1), hone x x.2⟩,
      (hρ.comp_continuous (continuous_subtype_val.prodMk continuous_const)
        (fun x => ⟨x.2, zero_le_one, le_rfl⟩)).subtype_mk _⟩
  let H : ContinuousMap.Homotopy i (j.comp g) :=
    { toFun := fun p => ⟨ρ (p.2, p.1), hρS ⟨p.2.2, p.1.2⟩⟩
      continuous_toFun := (hρ.comp_continuous
        ((continuous_subtype_val.comp continuous_snd).prodMk
          (continuous_subtype_val.comp continuous_fst))
        (fun p => ⟨p.2.2, p.1.2⟩)).subtype_mk _
      map_zero_left := fun x => Subtype.ext (hzero x x.2)
      map_one_left := fun _ => rfl }
  obtain ⟨c, hc⟩ := ((id_nullhomotopic D).comp_left g).comp_right j
  exact ⟨c, (show i.Homotopic (j.comp g) from ⟨H⟩).trans hc⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.nullhomotopic_inclusion_of_cylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.nullhomotopic_inclusion_of_cylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.nullhomotopic_inclusion_of_cylinder ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.nullhomotopic_inclusion_of_cylinder

end DifferentialGeometry.Topology.PiecewiseLinear
