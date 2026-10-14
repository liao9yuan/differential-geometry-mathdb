import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.Order.IntermediateValue
import Submission.DifferentialGeometry.Topology.SphereSeparation.LocalSides
import Submission.DifferentialGeometry.Topology.SphereSeparation.SameDimension
import Submission.DifferentialGeometry.Topology.SphereSeparation.StandardSphere

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Function _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.SphereSeparation

def AxialInterval (a : ℝ) : TopologicalSpace.Opens ℝ :=
  ⟨Ioo (-a) a, isOpen_Ioo⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.AxialInterval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.AxialInterval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.AxialInterval ``Submission.DifferentialGeometry.Topology.SphereSeparation.AxialInterval


def axialZero {a : ℝ} (ha : 0 < a) : AxialInterval a :=
  ⟨0, neg_lt_zero.mpr ha, ha⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.axialZero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.axialZero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.axialZero ``Submission.DifferentialGeometry.Topology.SphereSeparation.axialZero


def negativeHalfDomain {a : ℝ} (ha : 0 < a) :
    Set (SphereTwo × AxialInterval a) :=
  Set.univ ×ˢ _root_.Set.Iio (axialZero ha)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.negativeHalfDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.negativeHalfDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.negativeHalfDomain ``Submission.DifferentialGeometry.Topology.SphereSeparation.negativeHalfDomain


def zeroSliceDomain {a : ℝ} (ha : 0 < a) :
    Set (SphereTwo × AxialInterval a) :=
  Set.univ ×ˢ {axialZero ha}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.zeroSliceDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.zeroSliceDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.zeroSliceDomain ``Submission.DifferentialGeometry.Topology.SphereSeparation.zeroSliceDomain


def positiveHalfDomain {a : ℝ} (ha : 0 < a) :
    Set (SphereTwo × AxialInterval a) :=
  Set.univ ×ˢ _root_.Set.Ioi (axialZero ha)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.positiveHalfDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.positiveHalfDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.positiveHalfDomain ``Submission.DifferentialGeometry.Topology.SphereSeparation.positiveHalfDomain


def negativeHalfImage {N : Type*} {a : ℝ}
    (Φ : SphereTwo × AxialInterval a → N) (ha : 0 < a) : Set N :=
  Φ '' negativeHalfDomain ha

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.negativeHalfImage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.negativeHalfImage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.negativeHalfImage ``Submission.DifferentialGeometry.Topology.SphereSeparation.negativeHalfImage


def zeroSliceImage {N : Type*} {a : ℝ}
    (Φ : SphereTwo × AxialInterval a → N) (ha : 0 < a) : Set N :=
  Φ '' zeroSliceDomain ha

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.zeroSliceImage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.zeroSliceImage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.zeroSliceImage ``Submission.DifferentialGeometry.Topology.SphereSeparation.zeroSliceImage


def positiveHalfImage {N : Type*} {a : ℝ}
    (Φ : SphereTwo × AxialInterval a → N) (ha : 0 < a) : Set N :=
  Φ '' positiveHalfDomain ha

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.positiveHalfImage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.positiveHalfImage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.positiveHalfImage ``Submission.DifferentialGeometry.Topology.SphereSeparation.positiveHalfImage

theorem isOpen_negativeHalfImage_of_isOpenEmbedding
    {N : Type*} [TopologicalSpace N] {a : ℝ}
    (ha : 0 < a) (Φ : SphereTwo × AxialInterval a → N)
    (hΦ : Topology.IsOpenEmbedding Φ) :
    IsOpen (negativeHalfImage Φ ha) :=
  hΦ.isOpenMap _ (isOpen_univ.prod isOpen_Iio)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.isOpen_negativeHalfImage_of_isOpenEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.isOpen_negativeHalfImage_of_isOpenEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.isOpen_negativeHalfImage_of_isOpenEmbedding ``Submission.DifferentialGeometry.Topology.SphereSeparation.isOpen_negativeHalfImage_of_isOpenEmbedding

theorem isOpen_positiveHalfImage_of_isOpenEmbedding
    {N : Type*} [TopologicalSpace N] {a : ℝ}
    (ha : 0 < a) (Φ : SphereTwo × AxialInterval a → N)
    (hΦ : Topology.IsOpenEmbedding Φ) :
    IsOpen (positiveHalfImage Φ ha) :=
  hΦ.isOpenMap _ (isOpen_univ.prod isOpen_Ioi)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.isOpen_positiveHalfImage_of_isOpenEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.isOpen_positiveHalfImage_of_isOpenEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.isOpen_positiveHalfImage_of_isOpenEmbedding ``Submission.DifferentialGeometry.Topology.SphereSeparation.isOpen_positiveHalfImage_of_isOpenEmbedding

private theorem negativeAxis_connected {a : ℝ} (ha : 0 < a) :
    IsConnected (_root_.Set.Iio (axialZero ha) : Set (AxialInterval a)) := by
  have hI : IsConnected (_root_.Set.Ioo (-a) 0) := isConnected_Ioo (neg_lt_zero.mpr ha)
  let _ : ConnectedSpace (_root_.Set.Ioo (-a) 0) := Subtype.connectedSpace hI
  let f : _root_.Set.Ioo (-a) 0 → AxialInterval a := fun r =>
    ⟨r.1, r.2.1, lt_trans r.2.2 ha⟩
  have hf : Continuous f := by fun_prop
  have hrange : Set.range f = _root_.Set.Iio (axialZero ha) := by
    ext r
    constructor
    · rintro ⟨q, rfl⟩
      exact q.2.2
    · intro hr
      exact ⟨⟨r.1, r.2.1, hr⟩, Subtype.ext rfl⟩
  rw [← hrange]
  exact isConnected_range hf

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.negativeAxis_connected
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.negativeAxis_connected target :: scope.openDecls } }

private theorem positiveAxis_connected {a : ℝ} (ha : 0 < a) :
    IsConnected (_root_.Set.Ioi (axialZero ha) : Set (AxialInterval a)) := by
  have hI : IsConnected (_root_.Set.Ioo 0 a) := isConnected_Ioo ha
  let _ : ConnectedSpace (_root_.Set.Ioo 0 a) := Subtype.connectedSpace hI
  let f : _root_.Set.Ioo 0 a → AxialInterval a := fun r =>
    ⟨r.1, lt_trans (neg_lt_zero.mpr ha) r.2.1, r.2.2⟩
  have hf : Continuous f := by fun_prop
  have hrange : Set.range f = _root_.Set.Ioi (axialZero ha) := by
    ext r
    constructor
    · rintro ⟨q, rfl⟩
      exact q.2.1
    · intro hr
      exact ⟨⟨r.1, hr, r.2.2⟩, Subtype.ext rfl⟩
  rw [← hrange]
  exact isConnected_range hf

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.positiveAxis_connected
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.positiveAxis_connected target :: scope.openDecls } }

theorem isConnected_negativeHalfImage
    {N : Type*} [TopologicalSpace N] {a : ℝ} (ha : 0 < a)
    (Φ : SphereTwo × AxialInterval a → N) (hΦ : Continuous Φ) :
    IsConnected (negativeHalfImage Φ ha) := by
  exact (isConnected_sphereTwo.prod (negativeAxis_connected ha)).image Φ
    hΦ.continuousOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.isConnected_negativeHalfImage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.isConnected_negativeHalfImage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.isConnected_negativeHalfImage ``Submission.DifferentialGeometry.Topology.SphereSeparation.isConnected_negativeHalfImage

theorem isConnected_positiveHalfImage
    {N : Type*} [TopologicalSpace N] {a : ℝ} (ha : 0 < a)
    (Φ : SphereTwo × AxialInterval a → N) (hΦ : Continuous Φ) :
    IsConnected (positiveHalfImage Φ ha) := by
  exact (isConnected_sphereTwo.prod (positiveAxis_connected ha)).image Φ
    hΦ.continuousOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.isConnected_positiveHalfImage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.isConnected_positiveHalfImage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.isConnected_positiveHalfImage ``Submission.DifferentialGeometry.Topology.SphereSeparation.isConnected_positiveHalfImage

theorem bicollar_halves_opposite
    {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    {a : ℝ} (ha : 0 < a) (Φ : SphereTwo × AxialInterval a → N)
    (hΦ : Manifold.IsSmoothEmbedding
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ))
      (𝓘(ℝ, EuclideanThree)) ∞ Φ)
    (d : SphereSides (zeroSliceImage Φ ha)) :
    Xor
      (negativeHalfImage Φ ha ⊆ d.compactSide ∧
        positiveHalfImage Φ ha ⊆ d.endSide)
      (negativeHalfImage Φ ha ⊆ d.endSide ∧
        positiveHalfImage Φ ha ⊆ d.compactSide) := by
  have hΦcont : Continuous Φ := hΦ.contMDiff.continuous
  have hneg : IsConnected (negativeHalfImage Φ ha) :=
    isConnected_negativeHalfImage ha Φ hΦcont
  have hpos : IsConnected (positiveHalfImage Φ ha) :=
    isConnected_positiveHalfImage ha Φ hΦcont
  have hnegCompl : negativeHalfImage Φ ha ⊆ (zeroSliceImage Φ ha)ᶜ := by
    intro y hyneg hyzero
    rcases hyneg with ⟨p, hp, rfl⟩
    rcases hyzero with ⟨q, hq, hqp⟩
    have hpq : q = p := hΦ.isEmbedding.injective hqp
    have hqzero : q.2 = axialZero ha := hq.2
    have hpneg : p.2 < axialZero ha := hp.2
    rw [← hpq, hqzero] at hpneg
    exact (lt_irrefl _ hpneg)
  have hposCompl : positiveHalfImage Φ ha ⊆ (zeroSliceImage Φ ha)ᶜ := by
    intro y hypos hyzero
    rcases hypos with ⟨p, hp, rfl⟩
    rcases hyzero with ⟨q, hq, hqp⟩
    have hpq : q = p := hΦ.isEmbedding.injective hqp
    have hqzero : q.2 = axialZero ha := hq.2
    have hppos : axialZero ha < p.2 := hp.2
    rw [← hpq, hqzero] at hppos
    exact (lt_irrefl _ hppos)
  have hopen : IsOpen (Set.range Φ) := by
    have hrank :
        Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) =
          Module.finrank ℝ EuclideanThree := by
      norm_num [Module.finrank_prod, Module.finrank_fin_fun, EuclideanThree]
    exact Manifold.isOpen_range_of_isSmoothEmbedding
      (I := ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ)))
      (J := 𝓘(ℝ, EuclideanThree)) hrank hΦ
  have hzeroNonempty : (zeroSliceImage Φ ha).Nonempty := by
    obtain ⟨p, hp⟩ := isConnected_sphereTwo.nonempty
    exact ⟨Φ (p, axialZero ha), ⟨(p, axialZero ha), ⟨hp, rfl⟩, rfl⟩⟩
  have hzeroRange : zeroSliceImage Φ ha ⊆ Set.range Φ := by
    rintro y ⟨p, -, rfl⟩
    exact ⟨p, rfl⟩
  have hrangeDecomp :
      Set.range Φ ⊆
        (negativeHalfImage Φ ha ∪ zeroSliceImage Φ ha) ∪ positiveHalfImage Φ ha := by
    rintro y ⟨p, rfl⟩
    rcases lt_trichotomy p.2 (axialZero ha) with hp | hp | hp
    · exact Or.inl (Or.inl ⟨p, ⟨Set.mem_univ _, hp⟩, rfl⟩)
    · exact Or.inl (Or.inr ⟨p, ⟨Set.mem_univ _, hp⟩, rfl⟩)
    · exact Or.inr ⟨p, ⟨Set.mem_univ _, hp⟩, rfl⟩
  exact d.neighborhood_halves_opposite hzeroNonempty hneg hpos
    hnegCompl hposCompl hopen hzeroRange hrangeDecomp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.bicollar_halves_opposite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.bicollar_halves_opposite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.bicollar_halves_opposite ``Submission.DifferentialGeometry.Topology.SphereSeparation.bicollar_halves_opposite

end DifferentialGeometry.Topology.SphereSeparation
