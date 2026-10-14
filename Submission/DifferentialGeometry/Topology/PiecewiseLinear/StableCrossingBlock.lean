/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SingularGeneralPosition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

def blockBox (r tlo : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | |p.1| ≤ r ∧ |p.2.1| ≤ r ∧ p.2.2 ∈ _root_.Set.Icc tlo r}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.blockBox then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.blockBox"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.blockBox ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.blockBox

def blockHalfPlane (tlo : ℝ) : Set (ℝ × ℝ) :=
  {p | tlo = 0 → 0 ≤ p.2}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.blockHalfPlane then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.blockHalfPlane"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.blockHalfPlane ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.blockHalfPlane

section Ambient

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]

def chartBlock (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) (r tlo : ℝ) : Set M :=
  ec.source ∩ ⇑ec ⁻¹' (⇑A ⁻¹' blockBox r tlo)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.chartBlock then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.chartBlock"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.chartBlock ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.chartBlock

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem chartBlock_mono_of_half (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) {r tlo : ℝ} (hr : 0 ≤ r) (ht : tlo ≤ 0) :
    chartBlock ec A (r / 2) (tlo / 2) ⊆ chartBlock ec A r tlo := by
  intro x hx
  obtain ⟨hxs, hxb⟩ := hx
  refine ⟨hxs, ?_⟩
  simp only [_root_.Set.mem_preimage, blockBox, _root_.Set.mem_ofPred_eq, _root_.Set.mem_Icc] at hxb ⊢
  exact ⟨hxb.1.trans (by linarith), hxb.2.1.trans (by linarith),
    by linarith [hxb.2.2.1], by linarith [hxb.2.2.2]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.chartBlock_mono_of_half then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.chartBlock_mono_of_half"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.chartBlock_mono_of_half ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.chartBlock_mono_of_half

def innerChartBlock (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) (r tlo : ℝ) : Set M :=
  chartBlock ec A (r / 2) (tlo / 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.innerChartBlock then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.innerChartBlock"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.innerChartBlock ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.innerChartBlock

noncomputable def blockSheetProjA (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) (f : EuclideanSpace ℝ (Fin 2) → M) :
    EuclideanSpace ℝ (Fin 2) → ℝ × ℝ :=
  fun x => ((A (ec (f x))).2.1, (A (ec (f x))).2.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.blockSheetProjA then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.blockSheetProjA"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.blockSheetProjA ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.blockSheetProjA

noncomputable def blockSheetProjB (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) (f : EuclideanSpace ℝ (Fin 2) → M) :
    EuclideanSpace ℝ (Fin 2) → ℝ × ℝ :=
  fun x => ((A (ec (f x))).1, (A (ec (f x))).2.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.blockSheetProjB then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.blockSheetProjB"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.blockSheetProjB ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.blockSheetProjB

def IsStableCrossingBlock (f : EuclideanSpace ℝ (Fin 2) → M)
    (S : Set (EuclideanSpace ℝ (Fin 2)))
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (BdM : Set M)
    (A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) (r tlo : ℝ)
    (SA SB : Set (EuclideanSpace ℝ (Fin 2))) (a b : ℝ × ℝ → ℝ) (La Lb η : ℝ) : Prop :=
  0 < r ∧ 0 < η ∧ 0 ≤ La ∧ 0 ≤ Lb ∧ La * Lb ≤ 1 - η ∧
    IsCompact (closure (chartBlock ec A r tlo)) ∧
    closure (chartBlock ec A r tlo) ⊆ ec.source ∧
    ((tlo = -r ∧ Disjoint (chartBlock ec A r tlo) BdM) ∨
        (tlo = 0 ∧ (∀ z, (A z).2.2 = ℓ z) ∧
          ∀ x ∈ SA ∪ SB, (x ∈ frontier S ↔ (A (ec (f x))).2.2 = 0))) ∧
    S ∩ f ⁻¹' chartBlock ec A r tlo = SA ∪ SB ∧ Disjoint SA SB ∧
    (∀ x ∈ SA, (A (ec (f x))).1 = a ((A (ec (f x))).2.1, (A (ec (f x))).2.2)) ∧
    (∀ x ∈ SB, (A (ec (f x))).2.1 = b ((A (ec (f x))).1, (A (ec (f x))).2.2)) ∧
    IsPLHomeomorphOn (blockSheetProjA ec A f) SA (blockSheetProjA ec A f '' SA) ∧
    IsPLHomeomorphOn (blockSheetProjB ec A f) SB (blockSheetProjB ec A f '' SB) ∧
    (∀ x ∈ SA, f x ∈ innerChartBlock ec A r tlo → SA ∈ 𝓝[S] x ∧
      blockSheetProjA ec A f '' SA ∈ 𝓝[blockHalfPlane tlo] (blockSheetProjA ec A f x)) ∧
    (∀ x ∈ SB, f x ∈ innerChartBlock ec A r tlo → SB ∈ 𝓝[S] x ∧
      blockSheetProjB ec A f '' SB ∈ 𝓝[blockHalfPlane tlo] (blockSheetProjB ec A f x)) ∧
    (∀ v v' t : ℝ, |a (v, t) - a (v', t)| ≤ La * |v - v'|) ∧
    (∀ u u' t : ℝ, |b (u, t) - b (u', t)| ≤ Lb * |u - u'|) ∧
    IsPiecewiseAffineOn a _root_.Set.univ ∧ IsPiecewiseAffineOn b _root_.Set.univ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsStableCrossingBlock then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsStableCrossingBlock"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsStableCrossingBlock ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsStableCrossingBlock

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem IsStableCrossingBlock.margin_pos {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ}
    (h : IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η) : 0 < η :=
  h.2.1

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsStableCrossingBlock
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsStableCrossingBlock.margin_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsStableCrossingBlock.margin_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsStableCrossingBlock.margin_pos ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsStableCrossingBlock.margin_pos

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem sheets_nonempty_of_isStableCrossingBlock {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ}
    (h : IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η) {y : M}
    (hy : y ∈ doublePointSet f S) (hyB : y ∈ chartBlock ec A r tlo) :
    (SA ∩ f ⁻¹' {y}).Nonempty ∧ (SB ∩ f ⁻¹' {y}).Nonempty := by
  obtain ⟨-, -, -, -, -, -, -, -, hpre, -, -, -, hplA, hplB, -, -, -, -, -, -⟩ := h
  obtain ⟨x, hxS, z, hzS, hxz, hxy, hzy⟩ := hy
  have hfeq : f x = f z := by rw [hxy, hzy]
  have hxmem : x ∈ SA ∪ SB := by
    rw [← hpre]
    exact ⟨hxS, by simp only [_root_.Set.mem_preimage, hxy]; exact hyB⟩
  have hzmem : z ∈ SA ∪ SB := by
    rw [← hpre]
    exact ⟨hzS, by simp only [_root_.Set.mem_preimage, hzy]; exact hyB⟩
  have hnotA : ¬(x ∈ SA ∧ z ∈ SA) := by
    rintro ⟨hxA, hzA⟩
    exact hxz (hplA.bijOn.injOn hxA hzA (by simp only [blockSheetProjA, hfeq]))
  have hnotB : ¬(x ∈ SB ∧ z ∈ SB) := by
    rintro ⟨hxB, hzB⟩
    exact hxz (hplB.bijOn.injOn hxB hzB (by simp only [blockSheetProjB, hfeq]))
  rcases hxmem with hxA | hxB
  · rcases hzmem with hzA | hzB
    · exact absurd ⟨hxA, hzA⟩ hnotA
    · exact ⟨⟨x, hxA, hxy⟩, ⟨z, hzB, hzy⟩⟩
  · rcases hzmem with hzA | hzB
    · exact ⟨⟨z, hzA, hzy⟩, ⟨x, hxB, hxy⟩⟩
    · exact absurd ⟨hxB, hzB⟩ hnotB

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.sheets_nonempty_of_isStableCrossingBlock then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.sheets_nonempty_of_isStableCrossingBlock"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.sheets_nonempty_of_isStableCrossingBlock ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.sheets_nonempty_of_isStableCrossingBlock

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem eq_of_snd_eq_of_isStableCrossingBlock {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ}
    (h : IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η) {y z : M}
    (hy : y ∈ doublePointSet f S) (hyB : y ∈ chartBlock ec A r tlo)
    (hz : z ∈ doublePointSet f S) (hzB : z ∈ chartBlock ec A r tlo)
    (ht : (A (ec y)).2.2 = (A (ec z)).2.2) : y = z := by
  have hgraph : ∀ p : M, p ∈ doublePointSet f S → p ∈ chartBlock ec A r tlo →
      (A (ec p)).1 = a ((A (ec p)).2.1, (A (ec p)).2.2) ∧
        (A (ec p)).2.1 = b ((A (ec p)).1, (A (ec p)).2.2) := by
    intro p hp hpB
    obtain ⟨⟨x, hxA, hxp⟩, ⟨x', hx'B, hx'p⟩⟩ :=
      sheets_nonempty_of_isStableCrossingBlock h hp hpB
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hgA, hgB, -, -, -, -, -, -, -, -⟩ := h
    have hfx : f x = p := hxp
    have hfx' : f x' = p := hx'p
    exact ⟨by simpa only [hfx] using hgA x hxA, by simpa only [hfx'] using hgB x' hx'B⟩
  obtain ⟨hay, hby⟩ := hgraph y hy hyB
  obtain ⟨haz, hbz⟩ := hgraph z hz hzB
  obtain ⟨-, hη, hLa, hLb, hmar, -, -, -, -, -, -, -, -, -, -, -, hLipa, hLipb, -, -⟩ := h
  have hP : (0 : ℝ) ≤ |(A (ec y)).1 - (A (ec z)).1| := abs_nonneg _
  have hQ : (0 : ℝ) ≤ |(A (ec y)).2.1 - (A (ec z)).2.1| := abs_nonneg _
  have h1 : |(A (ec y)).1 - (A (ec z)).1| ≤ La * |(A (ec y)).2.1 - (A (ec z)).2.1| := by
    rw [hay, haz, ht]
    exact hLipa _ _ _
  have h2 : |(A (ec y)).2.1 - (A (ec z)).2.1| ≤ Lb * |(A (ec y)).1 - (A (ec z)).1| := by
    rw [hby, hbz, ht]
    exact hLipb _ _ _
  have h3 : La * |(A (ec y)).2.1 - (A (ec z)).2.1| ≤ La * (Lb * |(A (ec y)).1 - (A (ec z)).1|) :=
    mul_le_mul_of_nonneg_left h2 hLa
  have h5 : La * Lb * |(A (ec y)).1 - (A (ec z)).1| ≤ (1 - η) * |(A (ec y)).1 - (A (ec z)).1| :=
    mul_le_mul_of_nonneg_right hmar hP
  have hu : (A (ec y)).1 = (A (ec z)).1 := by
    have hzero : |(A (ec y)).1 - (A (ec z)).1| = 0 := by
      by_contra hne
      have hpos : 0 < |(A (ec y)).1 - (A (ec z)).1| := lt_of_le_of_ne hP (Ne.symm hne)
      nlinarith [h1, h3, h5, hpos, hη]
    exact sub_eq_zero.mp (abs_eq_zero.mp hzero)
  have hv : (A (ec y)).2.1 = (A (ec z)).2.1 := by
    have hzero : |(A (ec y)).2.1 - (A (ec z)).2.1| = 0 := by
      have : |(A (ec y)).2.1 - (A (ec z)).2.1| ≤ 0 := by
        have hu0 : |(A (ec y)).1 - (A (ec z)).1| = 0 := by
          rw [hu, sub_self, abs_zero]
        nlinarith [h2, hu0]
      exact le_antisymm this hQ
    exact sub_eq_zero.mp (abs_eq_zero.mp hzero)
  have hAeq : A (ec y) = A (ec z) := Prod.ext_iff.2 ⟨hu, Prod.ext_iff.2 ⟨hv, ht⟩⟩
  have hecyz : ec y = ec z := by
    have := congrArg (⇑A.symm) hAeq
    simpa only [AffineEquiv.symm_apply_apply] using this
  exact ec.injOn hyB.1 hzB.1 hecyz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.eq_of_snd_eq_of_isStableCrossingBlock then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.eq_of_snd_eq_of_isStableCrossingBlock"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.eq_of_snd_eq_of_isStableCrossingBlock ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.eq_of_snd_eq_of_isStableCrossingBlock

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem eq_of_mem_wall_of_isStableCrossingBlock {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM Wl : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ}
    (h : IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η)
    (hwall : ∀ x ∈ chartBlock ec A r tlo, x ∈ Wl ↔ (A (ec x)).2.2 = 0) {y z : M}
    (hy : y ∈ doublePointSet f S) (hyB : y ∈ chartBlock ec A r tlo) (hyW : y ∈ Wl)
    (hz : z ∈ doublePointSet f S) (hzB : z ∈ chartBlock ec A r tlo) (hzW : z ∈ Wl) : y = z :=
  eq_of_snd_eq_of_isStableCrossingBlock h hy hyB hz hzB
    (((hwall y hyB).1 hyW).trans ((hwall z hzB).1 hzW).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.eq_of_mem_wall_of_isStableCrossingBlock then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.eq_of_mem_wall_of_isStableCrossingBlock"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.eq_of_mem_wall_of_isStableCrossingBlock ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.eq_of_mem_wall_of_isStableCrossingBlock

end Ambient

end DifferentialGeometry.Topology.PiecewiseLinear
