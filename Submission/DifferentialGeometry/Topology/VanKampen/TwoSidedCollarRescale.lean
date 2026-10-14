/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.Order.Interval.Set.IsoIoo
import Mathlib.Topology.Algebra.Field
import Submission.DifferentialGeometry.Topology.VanKampen.TwoSidedCollarSeparation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Set _root_.Topology

noncomputable section

universe u v

namespace DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar

def realHomeomorphIoo (a : ℝ) (ha : 0 < a) :
    ℝ ≃ₜ Set.Ioo (-a) a :=
  (orderIsoIooNegOneOne ℝ).toHomeomorph.trans <|
    (Homeomorph.image (affineHomeomorph a 0 ha.ne') (Set.Ioo (-1 : ℝ) 1)).trans <|
      Homeomorph.setCongr (by
        simpa using affineHomeomorph_image_Ioo a 0 (-1 : ℝ) 1 ha)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.realHomeomorphIoo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.realHomeomorphIoo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.realHomeomorphIoo ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.realHomeomorphIoo

@[simp]
theorem realHomeomorphIoo_zero (a : ℝ) (ha : 0 < a) :
    ((realHomeomorphIoo a ha 0 : Set.Ioo (-a) a) : ℝ) = 0 := by
  rw [realHomeomorphIoo]
  change a * ((orderIsoIooNegOneOne ℝ 0 : Set.Ioo (-1 : ℝ) (1 : ℝ)) : ℝ) + 0 = 0
  rw [orderIsoIooNegOneOne]
  change a * (0 / (1 + |(0 : ℝ)|)) + 0 = 0
  norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.realHomeomorphIoo_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.realHomeomorphIoo_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.realHomeomorphIoo_zero ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.realHomeomorphIoo_zero

theorem strictMono_realHomeomorphIoo (a : ℝ) (ha : 0 < a) :
    StrictMono (fun t : ℝ => ((realHomeomorphIoo a ha t : Set.Ioo (-a) a) : ℝ)) := by
  intro s t hst
  rw [realHomeomorphIoo]
  change a * ((orderIsoIooNegOneOne ℝ s : Set.Ioo (-1 : ℝ) 1) : ℝ) + 0 <
    a * ((orderIsoIooNegOneOne ℝ t : Set.Ioo (-1 : ℝ) 1) : ℝ) + 0
  have horder := (orderIsoIooNegOneOne ℝ).strictMono hst
  change ((orderIsoIooNegOneOne ℝ s : Set.Ioo (-1 : ℝ) 1) : ℝ) <
    ((orderIsoIooNegOneOne ℝ t : Set.Ioo (-1 : ℝ) 1) : ℝ) at horder
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.strictMono_realHomeomorphIoo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.strictMono_realHomeomorphIoo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.strictMono_realHomeomorphIoo ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.strictMono_realHomeomorphIoo

theorem realHomeomorphIoo_pos_iff (a : ℝ) (ha : 0 < a) (t : ℝ) :
    0 < ((realHomeomorphIoo a ha t : Set.Ioo (-a) a) : ℝ) ↔ 0 < t := by
  let f : ℝ → ℝ := fun u => ((realHomeomorphIoo a ha u : Set.Ioo (-a) a) : ℝ)
  have hf : StrictMono f := strictMono_realHomeomorphIoo a ha
  change 0 < f t ↔ 0 < t
  have hf0 : f 0 = 0 := realHomeomorphIoo_zero a ha
  simpa only [hf0] using (hf.lt_iff_lt : f 0 < f t ↔ 0 < t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.realHomeomorphIoo_pos_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.realHomeomorphIoo_pos_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.realHomeomorphIoo_pos_iff ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.realHomeomorphIoo_pos_iff

theorem realHomeomorphIoo_neg_iff (a : ℝ) (ha : 0 < a) (t : ℝ) :
    ((realHomeomorphIoo a ha t : Set.Ioo (-a) a) : ℝ) < 0 ↔ t < 0 := by
  let f : ℝ → ℝ := fun u => ((realHomeomorphIoo a ha u : Set.Ioo (-a) a) : ℝ)
  have hf : StrictMono f := strictMono_realHomeomorphIoo a ha
  change f t < 0 ↔ t < 0
  have hf0 : f 0 = 0 := realHomeomorphIoo_zero a ha
  simpa only [hf0] using (hf.lt_iff_lt : f t < f 0 ↔ t < 0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.realHomeomorphIoo_neg_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.realHomeomorphIoo_neg_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.realHomeomorphIoo_neg_iff ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.realHomeomorphIoo_neg_iff

def ofOpenInterval
    {S : Type v} [TopologicalSpace S] {X : Type u} [TopologicalSpace X]
    {e : S → X} {a : ℝ} (ha : 0 < a)
    (φ : S × Set.Ioo (-a) a → X)
    (hφ : _root_.Topology.IsOpenEmbedding φ)
    (hzero : ∀ s, φ (s, ⟨0, by constructor <;> linarith⟩) = e s) :
    TwoSidedCollar e := by
  let ψ : S × ℝ ≃ₜ S × Set.Ioo (-a) a :=
    (Homeomorph.refl S).prodCongr (realHomeomorphIoo a ha)
  refine
    { toFun := φ ∘ ψ
      isOpenEmbedding_toFun := hφ.comp ψ.isOpenEmbedding
      zero_eq := ?_ }
  intro s
  change φ (ψ (s, 0)) = e s
  rw [show ψ (s, 0) = (s, ⟨0, by constructor <;> linarith⟩) by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact realHomeomorphIoo_zero a ha]
  exact hzero s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.ofOpenInterval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.ofOpenInterval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.ofOpenInterval ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.ofOpenInterval

end DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar
