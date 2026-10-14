import Submission.DifferentialGeometry.Topology.Morse.Defs
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology

open scoped _root_.Manifold _root_.ContDiff _root_.ContinuousMap
open _root_.Set

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

def hessianAt (I : ModelWithCorners ℝ E H) (f : M → ℝ) (p : M) : QuadraticForm ℝ E :=
  Morse.chartHessianAt (fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hessianAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hessianAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hessianAt ``Submission.DifferentialGeometry.Topology.hessianAt

def morseIndex (I : ModelWithCorners ℝ E H) (f : M → ℝ) (p : M) : ℕ :=
  sigNeg (hessianAt I f p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.morseIndex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.morseIndex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.morseIndex ``Submission.DifferentialGeometry.Topology.morseIndex

structure MorseStrip (I : ModelWithCorners ℝ E H) (f : M → ℝ) (a b : ℝ) : Prop where
  smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f
  lt : a < b
  compact : IsCompact (f ⁻¹' _root_.Set.Icc a b)
  regular : ∀ x, f x = a ∨ f x = b → ¬ Morse.IsCriticalPointAt I f x
  nondegenerate : ∀ x, f x ∈ _root_.Set.Ioo a b →
    Morse.IsCriticalPointAt I f x → Morse.IsNondegenerateCriticalPointAt I f x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MorseStrip then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MorseStrip"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MorseStrip ``Submission.DifferentialGeometry.Topology.MorseStrip

structure ModifiedWithin (f : M → ℝ) (a b : ℝ) (g : M → ℝ) : Prop where
  eqOn : _root_.Set.EqOn g f (f ⁻¹' _root_.Set.Ioo a b)ᶜ
  mapsTo : _root_.Set.MapsTo g (f ⁻¹' _root_.Set.Ioo a b) (_root_.Set.Ioo a b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ModifiedWithin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ModifiedWithin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ModifiedWithin ``Submission.DifferentialGeometry.Topology.ModifiedWithin

def isSelfIndexing (I : ModelWithCorners ℝ E H) (f : M → ℝ) (a b : ℝ) : Prop :=
  ∀ p q, f p ∈ _root_.Set.Ioo a b → f q ∈ _root_.Set.Ioo a b →
    Morse.IsCriticalPointAt I f p → Morse.IsCriticalPointAt I f q →
    morseIndex I f p < morseIndex I f q → f p < f q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isSelfIndexing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isSelfIndexing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isSelfIndexing ``Submission.DifferentialGeometry.Topology.isSelfIndexing

def isHomotopyEquivInclusion {X : Type*} [TopologicalSpace X] (A B : Set X) : Prop :=
  ∃ e : A ≃ₕ B, ∀ x : A, (e x : X) = x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isHomotopyEquivInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isHomotopyEquivInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isHomotopyEquivInclusion ``Submission.DifferentialGeometry.Topology.isHomotopyEquivInclusion

namespace ModifiedWithin

variable {f g : M → ℝ} {a b : ℝ}

omit [TopologicalSpace M]

theorem refl (f : M → ℝ) (a b : ℝ) : ModifiedWithin f a b f :=
  ⟨fun _ _ => rfl, fun _ hx => hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ModifiedWithin.refl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ModifiedWithin.refl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ModifiedWithin.refl ``Submission.DifferentialGeometry.Topology.ModifiedWithin.refl

theorem preimage_Ioo (h : ModifiedWithin f a b g) : g ⁻¹' _root_.Set.Ioo a b = f ⁻¹' _root_.Set.Ioo a b := by
  ext x
  by_cases hx : f x ∈ _root_.Set.Ioo a b
  · exact ⟨fun _ => hx, fun _ => h.mapsTo hx⟩
  · simp only [_root_.Set.mem_preimage, h.eqOn hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ModifiedWithin.preimage_Ioo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ModifiedWithin.preimage_Ioo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ModifiedWithin.preimage_Ioo ``Submission.DifferentialGeometry.Topology.ModifiedWithin.preimage_Ioo

theorem preimage_Icc (h : ModifiedWithin f a b g) : g ⁻¹' _root_.Set.Icc a b = f ⁻¹' _root_.Set.Icc a b := by
  ext x
  by_cases hx : f x ∈ _root_.Set.Ioo a b
  · have hg := h.mapsTo hx
    exact ⟨fun _ => _root_.Set.Ioo_subset_Icc_self hx, fun _ => _root_.Set.Ioo_subset_Icc_self hg⟩
  · simp only [_root_.Set.mem_preimage, h.eqOn hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ModifiedWithin.preimage_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ModifiedWithin.preimage_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ModifiedWithin.preimage_Icc ``Submission.DifferentialGeometry.Topology.ModifiedWithin.preimage_Icc

theorem preimage_singleton_left (h : ModifiedWithin f a b g) : g ⁻¹' {a} = f ⁻¹' {a} := by
  ext x
  by_cases hx : f x ∈ _root_.Set.Ioo a b
  · have hg := h.mapsTo hx
    simp only [_root_.Set.mem_preimage, _root_.Set.mem_singleton_iff]
    exact ⟨fun h' => (hg.1.ne' h').elim, fun h' => (hx.1.ne' h').elim⟩
  · simp only [_root_.Set.mem_preimage, h.eqOn hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ModifiedWithin.preimage_singleton_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ModifiedWithin.preimage_singleton_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ModifiedWithin.preimage_singleton_left ``Submission.DifferentialGeometry.Topology.ModifiedWithin.preimage_singleton_left

theorem preimage_singleton_right (h : ModifiedWithin f a b g) : g ⁻¹' {b} = f ⁻¹' {b} := by
  ext x
  by_cases hx : f x ∈ _root_.Set.Ioo a b
  · have hg := h.mapsTo hx
    simp only [_root_.Set.mem_preimage, _root_.Set.mem_singleton_iff]
    exact ⟨fun h' => (hg.2.ne h').elim, fun h' => (hx.2.ne h').elim⟩
  · simp only [_root_.Set.mem_preimage, h.eqOn hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ModifiedWithin.preimage_singleton_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ModifiedWithin.preimage_singleton_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ModifiedWithin.preimage_singleton_right ``Submission.DifferentialGeometry.Topology.ModifiedWithin.preimage_singleton_right

theorem preimage_Iic_left (h : ModifiedWithin f a b g) : g ⁻¹' _root_.Set.Iic a = f ⁻¹' _root_.Set.Iic a := by
  ext x
  by_cases hx : f x ∈ _root_.Set.Ioo a b
  · have hg := h.mapsTo hx
    simp only [_root_.Set.mem_preimage, _root_.Set.mem_Iic]
    exact ⟨fun h' => absurd h' (not_le.mpr hg.1), fun h' => absurd h' (not_le.mpr hx.1)⟩
  · simp only [_root_.Set.mem_preimage, h.eqOn hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ModifiedWithin.preimage_Iic_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ModifiedWithin.preimage_Iic_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ModifiedWithin.preimage_Iic_left ``Submission.DifferentialGeometry.Topology.ModifiedWithin.preimage_Iic_left

theorem preimage_Iic_right (h : ModifiedWithin f a b g) : g ⁻¹' _root_.Set.Iic b = f ⁻¹' _root_.Set.Iic b := by
  ext x
  by_cases hx : f x ∈ _root_.Set.Ioo a b
  · have hg := h.mapsTo hx
    simp only [_root_.Set.mem_preimage, _root_.Set.mem_Iic]
    exact ⟨fun _ => hx.2.le, fun _ => hg.2.le⟩
  · simp only [_root_.Set.mem_preimage, h.eqOn hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ModifiedWithin.preimage_Iic_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ModifiedWithin.preimage_Iic_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ModifiedWithin.preimage_Iic_right ``Submission.DifferentialGeometry.Topology.ModifiedWithin.preimage_Iic_right

theorem trans {k : M → ℝ} (h₁ : ModifiedWithin f a b g) (h₂ : ModifiedWithin g a b k) :
    ModifiedWithin f a b k := by
  refine ⟨fun x hx => ?_, fun x hx => h₂.mapsTo (h₁.mapsTo hx)⟩
  have hx' : x ∈ (g ⁻¹' _root_.Set.Ioo a b)ᶜ := by
    rw [h₁.preimage_Ioo]
    exact hx
  exact (h₂.eqOn hx').trans (h₁.eqOn hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ModifiedWithin.trans then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ModifiedWithin.trans"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ModifiedWithin.trans ``Submission.DifferentialGeometry.Topology.ModifiedWithin.trans

end ModifiedWithin

theorem isHomotopyEquivInclusion_refl {X : Type*} [TopologicalSpace X] (A : Set X) :
    isHomotopyEquivInclusion A A :=
  ⟨ContinuousMap.HomotopyEquiv.refl A, fun _ => rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isHomotopyEquivInclusion_refl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isHomotopyEquivInclusion_refl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isHomotopyEquivInclusion_refl ``Submission.DifferentialGeometry.Topology.isHomotopyEquivInclusion_refl

theorem isHomotopyEquivInclusion.subset {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : isHomotopyEquivInclusion A B) : A ⊆ B := by
  obtain ⟨e, he⟩ := h
  intro x hx
  have hmem : ((e ⟨x, hx⟩ : B) : X) ∈ B := (e ⟨x, hx⟩).2
  rwa [he ⟨x, hx⟩] at hmem

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.isHomotopyEquivInclusion
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isHomotopyEquivInclusion.subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isHomotopyEquivInclusion.subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isHomotopyEquivInclusion.subset ``Submission.DifferentialGeometry.Topology.isHomotopyEquivInclusion.subset

end

end DifferentialGeometry.Topology
