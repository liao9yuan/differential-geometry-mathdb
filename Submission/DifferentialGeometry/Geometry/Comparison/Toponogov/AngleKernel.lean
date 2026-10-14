import Mathlib.Topology.MetricSpace.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Toponogov

universe u

structure AngleKernel (α : Type u) where
  angle : α → α → ℝ
  nonneg : ∀ a b, 0 ≤ angle a b
  self : ∀ a, angle a a = 0
  symm : ∀ a b, angle a b = angle b a
  triangle : ∀ a b c, angle a c ≤ angle a b + angle b c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.AngleKernel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.AngleKernel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.AngleKernel ``Submission.DifferentialGeometry.Toponogov.AngleKernel

namespace AngleKernel

variable {α : Type u} (K : AngleKernel α)

def setoid : Setoid α where
  r a b := K.angle a b = 0
  iseqv :=
    { refl := fun a => K.self a
      symm := fun {a b} h => by rw [K.symm b a]; exact h
      trans := fun {a b c} hab hbc => by
        have h := K.triangle a b c
        have h0 := K.nonneg a c
        rw [hab, hbc, add_zero] at h
        linarith }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.AngleKernel.setoid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.AngleKernel.setoid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.AngleKernel.setoid ``Submission.DifferentialGeometry.Toponogov.AngleKernel.setoid

def classOf : α → Quotient K.setoid := Quotient.mk K.setoid

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.AngleKernel.classOf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.AngleKernel.classOf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.AngleKernel.classOf ``Submission.DifferentialGeometry.Toponogov.AngleKernel.classOf

theorem angle_congr_left {a a' : α} (ha : K.angle a a' = 0) (b : α) :
    K.angle a b = K.angle a' b := by
  have hsym : K.angle a' a = 0 := by rw [K.symm a' a]; exact ha
  have h₁ : K.angle a b ≤ K.angle a' b := by
    have h := K.triangle a a' b
    rw [ha, zero_add] at h
    exact h
  have h₂ : K.angle a' b ≤ K.angle a b := by
    have h := K.triangle a' a b
    rw [hsym, zero_add] at h
    exact h
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.AngleKernel.angle_congr_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.AngleKernel.angle_congr_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.AngleKernel.angle_congr_left ``Submission.DifferentialGeometry.Toponogov.AngleKernel.angle_congr_left

theorem angle_congr_right {b b' : α} (hb : K.angle b b' = 0) (a : α) :
    K.angle a b = K.angle a b' := by
  have hsym : K.angle b' b = 0 := by rw [K.symm b' b]; exact hb
  have h₁ : K.angle a b' ≤ K.angle a b := by
    have h := K.triangle a b b'
    rw [hb, add_zero] at h
    exact h
  have h₂ : K.angle a b ≤ K.angle a b' := by
    have h := K.triangle a b' b
    rw [hsym, add_zero] at h
    exact h
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.AngleKernel.angle_congr_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.AngleKernel.angle_congr_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.AngleKernel.angle_congr_right ``Submission.DifferentialGeometry.Toponogov.AngleKernel.angle_congr_right

theorem angle_eq_of_rel {a₁ b₁ a₂ b₂ : α}
    (ha : K.angle a₁ a₂ = 0) (hb : K.angle b₁ b₂ = 0) :
    K.angle a₁ b₁ = K.angle a₂ b₂ :=
  (K.angle_congr_left ha b₁).trans (K.angle_congr_right hb a₂)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.AngleKernel.angle_eq_of_rel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.AngleKernel.angle_eq_of_rel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.AngleKernel.angle_eq_of_rel ``Submission.DifferentialGeometry.Toponogov.AngleKernel.angle_eq_of_rel

def dist : Quotient K.setoid → Quotient K.setoid → ℝ :=
  fun x y => Quotient.liftOn₂ (s₁ := K.setoid) (s₂ := K.setoid) x y K.angle
    (fun _a₁ _b₁ _a₂ _b₂ ha hb => K.angle_eq_of_rel ha hb)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.AngleKernel.dist then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.AngleKernel.dist"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.AngleKernel.dist ``Submission.DifferentialGeometry.Toponogov.AngleKernel.dist

theorem dist_mk (a b : α) : K.dist (K.classOf a) (K.classOf b) = K.angle a b :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.AngleKernel.dist_mk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.AngleKernel.dist_mk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.AngleKernel.dist_mk ``Submission.DifferentialGeometry.Toponogov.AngleKernel.dist_mk

theorem dist_self (x : Quotient K.setoid) : K.dist x x = 0 := by
  obtain ⟨a, rfl⟩ := Quotient.exists_rep x
  exact K.self a

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.AngleKernel.dist_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.AngleKernel.dist_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.AngleKernel.dist_self ``Submission.DifferentialGeometry.Toponogov.AngleKernel.dist_self

theorem dist_comm (x y : Quotient K.setoid) : K.dist x y = K.dist y x := by
  obtain ⟨a, rfl⟩ := Quotient.exists_rep x
  obtain ⟨b, rfl⟩ := Quotient.exists_rep y
  exact K.symm a b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.AngleKernel.dist_comm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.AngleKernel.dist_comm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.AngleKernel.dist_comm ``Submission.DifferentialGeometry.Toponogov.AngleKernel.dist_comm

theorem dist_triangle (x y z : Quotient K.setoid) :
    K.dist x z ≤ K.dist x y + K.dist y z := by
  obtain ⟨a, rfl⟩ := Quotient.exists_rep x
  obtain ⟨b, rfl⟩ := Quotient.exists_rep y
  obtain ⟨c, rfl⟩ := Quotient.exists_rep z
  exact K.triangle a b c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.AngleKernel.dist_triangle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.AngleKernel.dist_triangle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.AngleKernel.dist_triangle ``Submission.DifferentialGeometry.Toponogov.AngleKernel.dist_triangle

theorem eq_of_dist_eq_zero {x y : Quotient K.setoid} (h : K.dist x y = 0) : x = y := by
  obtain ⟨a, rfl⟩ := Quotient.exists_rep x
  obtain ⟨b, rfl⟩ := Quotient.exists_rep y
  exact Quotient.sound (show K.angle a b = 0 from h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.AngleKernel.eq_of_dist_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.AngleKernel.eq_of_dist_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.AngleKernel.eq_of_dist_eq_zero ``Submission.DifferentialGeometry.Toponogov.AngleKernel.eq_of_dist_eq_zero

theorem dist_nonneg (x y : Quotient K.setoid) : 0 ≤ K.dist x y := by
  obtain ⟨a, rfl⟩ := Quotient.exists_rep x
  obtain ⟨b, rfl⟩ := Quotient.exists_rep y
  exact K.nonneg a b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.AngleKernel.dist_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.AngleKernel.dist_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.AngleKernel.dist_nonneg ``Submission.DifferentialGeometry.Toponogov.AngleKernel.dist_nonneg

@[instance_reducible]
def metricSpace : MetricSpace (Quotient K.setoid) where
  dist := K.dist
  dist_self := fun x => K.dist_self x
  dist_comm := fun x y => K.dist_comm x y
  dist_triangle := fun x y z => K.dist_triangle x y z
  eq_of_dist_eq_zero := fun {x y} h => K.eq_of_dist_eq_zero h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.AngleKernel.metricSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.AngleKernel.metricSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.AngleKernel.metricSpace ``Submission.DifferentialGeometry.Toponogov.AngleKernel.metricSpace

theorem classOf_surjective : Function.Surjective K.classOf := Quotient.mk_surjective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.AngleKernel.classOf_surjective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.AngleKernel.classOf_surjective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.AngleKernel.classOf_surjective ``Submission.DifferentialGeometry.Toponogov.AngleKernel.classOf_surjective

end AngleKernel

end DifferentialGeometry.Toponogov
