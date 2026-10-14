/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.InwardPushComposition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Composition

variable {n m p : ℕ} {M N P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin p)) P]

theorem IsPLWithinAt.comp {f : M → N} {g : N → P} {s : Set M} {t : Set N} {x : M}
    (hg : IsPLWithinAt m p g t (f x)) (hf : IsPLWithinAt n m f s x) (hst : _root_.Set.MapsTo f s t) :
    IsPLWithinAt n p (g ∘ f) s x := by
  let e := chartAt (EuclideanSpace ℝ (Fin n)) x
  let e' := chartAt (EuclideanSpace ℝ (Fin m)) (f x)
  let e'' := chartAt (EuclideanSpace ℝ (Fin p)) (g (f x))
  have hx : x ∈ e.source := mem_chart_source _ _
  have hfx : f x ∈ e'.source := mem_chart_source _ _
  have hpre : f ⁻¹' e'.source ∈ 𝓝[s] x :=
    hf.continuousWithinAt.preimage_mem_nhdsWithin (e'.open_source.mem_nhds hfx)
  refine (piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_inter' hpre).mp ?_
  have hsub : s ∩ f ⁻¹' e'.source ⊆ s := _root_.Set.inter_subset_left
  have hnb : s ∩ f ⁻¹' e'.source ∈ 𝓝[s] x := Filter.inter_mem self_mem_nhdsWithin hpre
  have hf' : IsPLWithinAt n m f (s ∩ f ⁻¹' e'.source) x := hf.mono_of_mem_nhdsWithin hsub hnb
  refine ⟨hg.continuousWithinAt.comp hf'.continuousWithinAt (hst.mono_left hsub), ?_⟩
  have hgcoord : IsPiecewiseAffineWithinAt (e'' ∘ g ∘ e'.symm) (e'.symm ⁻¹' t) (e' (f x)) :=
    hg.prop
  have hpoint : (e' ∘ f ∘ e.symm) (e x) = e' (f x) := by
    change e' (f (e.symm (e x))) = e' (f x)
    rw [e.left_inv hx]
  rw [← hpoint] at hgcoord
  have hcomp := hgcoord.comp hf'.prop
  have hset : e.symm ⁻¹' (s ∩ f ⁻¹' e'.source) ∩
      (e' ∘ f ∘ e.symm) ⁻¹' (e'.symm ⁻¹' t) = e.symm ⁻¹' (s ∩ f ⁻¹' e'.source) := by
    refine inter_eq_left.mpr fun z hz => ?_
    change e'.symm (e' (f (e.symm z))) ∈ t
    rw [e'.left_inv hz.2]
    exact hst hz.1
  rw [hset] at hcomp
  refine piecewiseAffineProperty_localInvariantProp.congr_nhdsWithin ?_ ?_ hcomp
  · filter_upwards [self_mem_nhdsWithin] with z hz
    change e'' (g (e'.symm (e' (f (e.symm z))))) = e'' (g (f (e.symm z)))
    rw [e'.left_inv hz.2]
  · change e'' (g (e'.symm (e' (f (e.symm (e x)))))) = e'' (g (f (e.symm (e x))))
    rw [e.left_inv hx, e'.left_inv hfx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLWithinAt.comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLWithinAt.comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLWithinAt.comp ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLWithinAt.comp

theorem IsPLOn.comp_of_mapsTo {f : M → N} {g : N → P} {s : Set M} {t : Set N}
    (hg : IsPLOn m p g t) (hf : IsPLOn n m f s) (hst : _root_.Set.MapsTo f s t) : IsPLOn n p (g ∘ f) s :=
  fun x hx => IsPLWithinAt.comp (hg (f x) (hst hx)) (hf x hx) hst

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLOn.comp_of_mapsTo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLOn.comp_of_mapsTo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLOn.comp_of_mapsTo ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLOn.comp_of_mapsTo

end Composition

section Glue

variable {X Y : Type*}

theorem exists_forall_eqOn_of_forall_le {A : ℕ → Set X} (F : ℕ → X → Y)
    (hF : ∀ i j, i ≤ j → _root_.Set.EqOn (F j) (F i) (A i)) : ∃ G : X → Y, ∀ i, _root_.Set.EqOn G (F i) (A i) := by
  classical
  refine ⟨fun x => if hx : ∃ i, x ∈ A i then F (Nat.find hx) x else F 0 x, fun i x hx => ?_⟩
  have hex : ∃ j, x ∈ A j := ⟨i, hx⟩
  simp only [dif_pos hex]
  exact (hF (Nat.find hex) i (Nat.find_min' hex hx) (Nat.find_spec hex)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_forall_eqOn_of_forall_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_forall_eqOn_of_forall_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_forall_eqOn_of_forall_le ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_forall_eqOn_of_forall_le

end Glue

section Stages

variable {n : ℕ} {M₁ M₂ : Type*} [TopologicalSpace M₁]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁] [MetricSpace M₂]

theorem exists_isPLOn_injOn_leftInvOn_dist_lt_of_stages {K : Set M₁} {h : M₁ → M₂}
    {ψ : M₁ → ℝ} {N G : ℕ → Set M₁} {P Q : ℕ → M₁ → M₁} {p q : M₁ → M₁}
    (hNmono : Monotone N) (hNK : ∀ i, N i ⊆ K) (hNcover : ∀ x ∈ K, ∃ i, x ∈ N i)
    (hNnhds : ∀ i, ∀ x ∈ N i, N (i + 1) ∈ 𝓝[K] x) (hGopen : ∀ i, IsOpen (G i))
    (hGint : ∀ i, G i ⊆ interior K) (hPG : ∀ i, _root_.Set.MapsTo (P i) (N i) (G i))
    (hPpl : ∀ i, IsPLOn n n (P i) K) (hPinj : ∀ i, _root_.Set.InjOn (P i) K)
    (hQpl : ∀ i, IsPLOn n n (Q i) (G i)) (hQK : ∀ i, _root_.Set.MapsTo (Q i) (G i) K)
    (hQP : ∀ i, _root_.Set.LeftInvOn (Q i) (P i) K)
    (hdist : ∀ i, ∀ x ∈ N i, _root_.Dist.dist (h (P i x)) (h x) < ψ x)
    (hp : ∀ i, _root_.Set.EqOn p (P i) (N i)) (hq : ∀ i, _root_.Set.EqOn q (Q i) (G i)) :
    ∃ W : Set M₁, IsOpen W ∧ W ⊆ interior K ∧ _root_.Set.MapsTo p K W ∧
      IsPLOn n n p K ∧ _root_.Set.InjOn p K ∧ IsPLOn n n q W ∧ _root_.Set.MapsTo q W K ∧ _root_.Set.LeftInvOn q p K ∧
      ∀ x ∈ K, _root_.Dist.dist (h (p x)) (h x) < ψ x := by
  refine ⟨⋃ i, G i, isOpen_iUnion hGopen, _root_.Set.iUnion_subset hGint, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := hNcover x hx
    refine mem_iUnion.mpr ⟨i, ?_⟩
    rw [hp i hi]
    exact hPG i hi
  · intro x hx
    obtain ⟨i, hi⟩ := hNcover x hx
    have hmem : x ∈ N (i + 1) := hNmono (Nat.le_succ i) hi
    have hnb : N (i + 1) ∈ 𝓝[K] x := hNnhds i x hi
    have hbase : IsPLWithinAt n n (P (i + 1)) (N (i + 1)) x :=
      IsPLWithinAt.mono_of_mem_nhdsWithin (hPpl (i + 1) x hx) (hNK (i + 1)) hnb
    have hcongr : IsPLWithinAt n n p (N (i + 1)) x :=
      piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_of_mem hbase
        (fun y hy => hp (i + 1) hy) hmem
    refine (piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_inter' hnb).mp ?_
    rw [inter_eq_right.mpr (hNK (i + 1))]
    exact hcongr
  · intro x hx y hy hxy
    obtain ⟨i, hi⟩ := hNcover x hx
    obtain ⟨j, hj⟩ := hNcover y hy
    have hi' : x ∈ N (_root_.Max.max i j) := hNmono (le_max_left i j) hi
    have hj' : y ∈ N (_root_.Max.max i j) := hNmono (le_max_right i j) hj
    refine hPinj (_root_.Max.max i j) hx hy ?_
    rw [← hp (_root_.Max.max i j) hi', ← hp (_root_.Max.max i j) hj']
    exact hxy
  · intro y hy
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    have hcongr : IsPLWithinAt n n q (G i) y :=
      piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_of_mem (hQpl i y hi)
        (fun z hz => hq i hz) hi
    have hset : (fun z => z ∈ G i) =ᶠ[𝓝 y] (fun z => z ∈ ⋃ j, G j) := by
      filter_upwards [(hGopen i).mem_nhds hi] with z hz
      apply propext
      exact ⟨fun _ => mem_iUnion.mpr ⟨i, hz⟩, fun _ => hz⟩
    exact (piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_set hset).mp hcongr
  · intro y hy
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    rw [hq i hi]
    exact hQK i hi
  · intro x hx
    obtain ⟨i, hi⟩ := hNcover x hx
    rw [hp i hi, hq i (hPG i hi)]
    exact hQP i hx
  · intro x hx
    obtain ⟨i, hi⟩ := hNcover x hx
    rw [hp i hi]
    exact hdist i x hi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLOn_injOn_leftInvOn_dist_lt_of_stages then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLOn_injOn_leftInvOn_dist_lt_of_stages"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLOn_injOn_leftInvOn_dist_lt_of_stages ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLOn_injOn_leftInvOn_dist_lt_of_stages

theorem exists_isPLOn_injOn_leftInvOn_dist_lt_of_stage_family {K : Set M₁} {h : M₁ → M₂}
    {ψ : M₁ → ℝ} {N G : ℕ → Set M₁} {P Q : ℕ → M₁ → M₁}
    (hNmono : Monotone N) (hNK : ∀ i, N i ⊆ K) (hNcover : ∀ x ∈ K, ∃ i, x ∈ N i)
    (hNnhds : ∀ i, ∀ x ∈ N i, N (i + 1) ∈ 𝓝[K] x) (hGopen : ∀ i, IsOpen (G i))
    (hGint : ∀ i, G i ⊆ interior K) (hPG : ∀ i, _root_.Set.MapsTo (P i) (N i) (G i))
    (hPpl : ∀ i, IsPLOn n n (P i) K) (hPinj : ∀ i, _root_.Set.InjOn (P i) K)
    (hQpl : ∀ i, IsPLOn n n (Q i) (G i)) (hQK : ∀ i, _root_.Set.MapsTo (Q i) (G i) K)
    (hQP : ∀ i, _root_.Set.LeftInvOn (Q i) (P i) K)
    (hdist : ∀ i, ∀ x ∈ N i, _root_.Dist.dist (h (P i x)) (h x) < ψ x)
    (hPstab : ∀ i j, i ≤ j → _root_.Set.EqOn (P j) (P i) (N i))
    (hQstab : ∀ i j, i ≤ j → _root_.Set.EqOn (Q j) (Q i) (G i)) :
    ∃ p q : M₁ → M₁, ∃ W : Set M₁, IsOpen W ∧ W ⊆ interior K ∧ _root_.Set.MapsTo p K W ∧
      IsPLOn n n p K ∧ _root_.Set.InjOn p K ∧ IsPLOn n n q W ∧ _root_.Set.MapsTo q W K ∧ _root_.Set.LeftInvOn q p K ∧
      ∀ x ∈ K, _root_.Dist.dist (h (p x)) (h x) < ψ x := by
  obtain ⟨p, hp⟩ := exists_forall_eqOn_of_forall_le (A := N) P hPstab
  obtain ⟨q, hq⟩ := exists_forall_eqOn_of_forall_le (A := G) Q hQstab
  obtain ⟨W, hW⟩ := exists_isPLOn_injOn_leftInvOn_dist_lt_of_stages hNmono hNK hNcover hNnhds
    hGopen hGint hPG hPpl hPinj hQpl hQK hQP hdist hp hq
  exact ⟨p, q, W, hW⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLOn_injOn_leftInvOn_dist_lt_of_stage_family then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLOn_injOn_leftInvOn_dist_lt_of_stage_family"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLOn_injOn_leftInvOn_dist_lt_of_stage_family ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLOn_injOn_leftInvOn_dist_lt_of_stage_family

end Stages

section Witness

variable {M₁ M₂ : Type*} [TopologicalSpace M₁] [T2Space M₁]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁] [MetricSpace M₂]

theorem exists_isPLOn_injOn_leftInvOn_dist_lt_of_one_stage {K : Set M₁}
    (hK : IsPolyhedralManifoldWithBoundary (n := 3) 3 K) {h : M₁ → M₂} (hh : ContinuousOn h K)
    {ψ : M₁ → ℝ} (hψ : ContinuousOn ψ K) (hψpos : ∀ x ∈ K, 0 < ψ x) :
    ∃ p q : M₁ → M₁, ∃ W : Set M₁, IsOpen W ∧ W ⊆ interior K ∧ _root_.Set.MapsTo p K W ∧
      IsPLOn 3 3 p K ∧ _root_.Set.InjOn p K ∧ IsPLOn 3 3 q W ∧ _root_.Set.MapsTo q W K ∧ _root_.Set.LeftInvOn q p K ∧
      ∀ x ∈ K, _root_.Dist.dist (h (p x)) (h x) < ψ x := by
  obtain ⟨p, q, W, hWopen, hWK, hpW, hppl, hpinj, hqpl, hqK, hinv, hpdist⟩ :=
    hK.exists_isPLOn_injOn_leftInvOn_dist_lt hh hψ hψpos
  exact exists_isPLOn_injOn_leftInvOn_dist_lt_of_stage_family (N := fun _ => K)
    (G := fun _ => W) (P := fun _ => p) (Q := fun _ => q) monotone_const (fun _ => Subset.rfl)
    (fun x hx => ⟨0, hx⟩) (fun _ x _ => self_mem_nhdsWithin) (fun _ => hWopen) (fun _ => hWK)
    (fun _ => hpW) (fun _ => hppl) (fun _ => hpinj) (fun _ => hqpl) (fun _ => hqK)
    (fun _ => hinv) (fun _ x hx => hpdist x hx) (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLOn_injOn_leftInvOn_dist_lt_of_one_stage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLOn_injOn_leftInvOn_dist_lt_of_one_stage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLOn_injOn_leftInvOn_dist_lt_of_one_stage ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLOn_injOn_leftInvOn_dist_lt_of_one_stage

end Witness

end DifferentialGeometry.Topology.PiecewiseLinear
