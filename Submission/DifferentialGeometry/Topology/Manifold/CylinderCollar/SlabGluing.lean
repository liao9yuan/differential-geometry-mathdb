import Submission.DifferentialGeometry.Topology.Manifold.CylinderCollar.SlabMatching
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.CompactGluing

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Filter _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.Manifold

local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]

theorem exists_slab_concatenation_of_eq
    (P Q : PartialDiffeomorph SphereCylinderModel I SphereCylinder M ∞)
    (hP : _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ P.source)
    (hQ : _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ Q.source)
    (hzero : ∀ z : S2, Q (z,0) = P (z,1))
    (hmeet : P '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∩ Q '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) =
      P '' (_root_.Set.univ ×ˢ ({1} : Set ℝ))) :
    ∃ R : PartialDiffeomorph SphereCylinderModel I SphereCylinder M ∞,
      _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 2 ⊆ R.source ∧
      R '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 2) =
        P '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∪ Q '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∧
      (∀ z : S2, R (z,0) = P (z,0)) ∧ (∀ z : S2, R (z,2) = Q (z,1)) ∧
      (∀ z : S2, R =ᶠ[𝓝 (z,0)] P) ∧
      ∀ z : S2, R =ᶠ[𝓝 (z,2)] (fun q => Q (q.1,q.2-1)) := by
  obtain ⟨r,hr,F,hF,hF0,hfix,hband⟩ := exists_slab_collar_matching P Q hP hQ hzero hmeet
  let S : SphereCylinder ≃ₘ⟮SphereCylinderModel,SphereCylinderModel⟯ SphereCylinder :=
    Diffeomorph.fiberwiseAffine (fun _ => (-1:ℝ)) (fun _ => (1:ℝ))
      contMDiff_const contMDiff_const (fun _ => one_ne_zero)
  have hS (q : SphereCylinder) : S q = (q.1,q.2-1) := by
    change (q.1,-1+1*q.2) = _
    congr 1
    ring
  let Q' := (S.trans F).toPartialDiffeomorph.trans Q
  let K₀ : Set SphereCylinder := _root_.Set.univ ×ˢ _root_.Set.Icc (0:ℝ) 1
  let K₁ : Set SphereCylinder := _root_.Set.univ ×ˢ _root_.Set.Icc (1:ℝ) 2
  have hK : K₀ ∪ K₁ = _root_.Set.univ ×ˢ _root_.Set.Icc (0:ℝ) 2 := by
    ext q
    simp only [K₀,K₁,_root_.Set.mem_union,_root_.Set.mem_prod,_root_.Set.mem_univ,true_and,_root_.Set.mem_Icc]
    constructor
    · rintro (h | h) <;> constructor <;> linarith [h.1,h.2]
    · intro h
      by_cases hq : q.2 ≤ 1
      · exact Or.inl ⟨h.1,hq⟩
      · exact Or.inr ⟨(le_of_not_ge hq),h.2⟩
  have hshift : S '' K₁ = _root_.Set.univ ×ˢ _root_.Set.Icc (0:ℝ) 1 := by
    ext q
    constructor
    · rintro ⟨p,hp,rfl⟩
      rw [hS]
      exact ⟨mem_univ _,by linarith [hp.2.1],by linarith [hp.2.2]⟩
    · rintro ⟨_,hq0,hq1⟩
      refine ⟨(q.1,q.2+1),⟨mem_univ _,by linarith,by linarith⟩,?_⟩
      rw [hS]
      simp only [add_sub_cancel_right,Prod.mk.eta]
  have hQ's : K₁ ⊆ Q'.source := by
    intro q hq
    refine ⟨mem_univ _,hQ ?_⟩
    change F (S q) ∈ _root_.Set.univ ×ˢ _root_.Set.Icc (0:ℝ) 1
    rw [← hband]
    exact ⟨S q,hshift ▸ _root_.Set.mem_image_of_mem S hq,rfl⟩
  have hQ'image : Q' '' K₁ = Q '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0:ℝ) 1) := by
    calc
      Q' '' K₁ = Q '' (F '' (S '' K₁)) := by
        simp only [_root_.Set.image_image]
        rfl
      _ = Q '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0:ℝ) 1) := by rw [hshift,hband]
  let O : Set SphereCylinder := {q | |q.2-1| < r}
  have hO : IsOpen O := isOpen_lt (continuous_abs.comp (continuous_snd.sub continuous_const)) continuous_const
  have heq : _root_.Set.EqOn P Q' O := by
    intro q hq
    have hh := (hF (S q) (by rw [hS]; exact hq.le)).2
    change P q = Q (F (S q))
    rw [hh,hS]
    congr 1
    ext <;> simp
  have hKO : K₀ ∩ K₁ ⊆ O := by
    intro q hq
    have he : q.2 = 1 := le_antisymm hq.1.2.2 hq.2.2.1
    change |q.2-1| < r
    simpa only [he,sub_self,abs_zero] using hr
  have himage : P '' K₀ ∩ Q' '' K₁ ⊆ P '' (K₀ ∩ K₁) := by
    rw [hQ'image,hmeet]
    apply _root_.Set.image_mono
    rintro q ⟨_,hq⟩
    exact ⟨⟨mem_univ _,by rw [hq]; constructor <;> norm_num⟩,
      ⟨mem_univ _,by rw [hq]; constructor <;> norm_num⟩⟩
  obtain ⟨R,U₀,U₁,hU₀,hU₁,h₀,h₁,hs,hR₀,hR₁⟩ :=
    P.exists_eqOn_neighborhoods_of_isCompact Q' (isCompact_univ.prod _root_.CompactIccSpace.isCompact_Icc)
      (isCompact_univ.prod _root_.CompactIccSpace.isCompact_Icc) hP hQ's hO hKO heq himage
  have hclosed : _root_.Set.univ ×ˢ _root_.Set.Icc (0:ℝ) 2 ⊆ R.source := by
    rw [← hK]
    exact (_root_.Set.union_subset_union h₀ h₁).trans hs
  have himg : R '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0:ℝ) 2) = P '' K₀ ∪ Q' '' K₁ := by
    rw [← hK,_root_.Set.image_union]
    congr 1
    · exact _root_.Set.image_congr (fun q hq => hR₀ (h₀ hq))
    · exact _root_.Set.image_congr (fun q hq => hR₁ (h₁ hq))
  have hnear0 (z : S2) : R =ᶠ[𝓝 (z,0)] P :=
    _root_.Filter.eventuallyEq_of_mem (hU₀.mem_nhds (h₀ ⟨mem_univ _,by constructor <;> norm_num⟩)) hR₀
  have hnear2 (z : S2) : R =ᶠ[𝓝 (z,2)] (fun q => Q (q.1,q.2-1)) := by
    filter_upwards [hU₁.mem_nhds (h₁ ⟨mem_univ _,by constructor <;> norm_num⟩),
      continuous_snd.continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds (by norm_num : (3/2:ℝ)<2))] with q hq hqt
    rw [hR₁ hq]
    change Q (F (S q)) = _
    rw [hfix (S q) (by rw [hS]; change (1/2:ℝ) ≤ q.2-1; change (3/2:ℝ) < q.2 at hqt; linarith),hS]
  refine ⟨R,hclosed,?_,?_,?_,hnear0,hnear2⟩
  · exact himg.trans (congrArg (fun U => P '' K₀ ∪ U) hQ'image)
  · intro z
    exact (hnear0 z).eq_of_nhds
  · intro z
    have h := (hnear2 z).eq_of_nhds
    simpa only [show (2:ℝ)-1=1 by norm_num] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_slab_concatenation_of_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_slab_concatenation_of_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_slab_concatenation_of_eq ``Submission.DifferentialGeometry.Topology.Manifold.exists_slab_concatenation_of_eq

theorem exists_slab_concatenation
    (P Q : PartialDiffeomorph SphereCylinderModel I SphereCylinder M ∞)
    (η : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2)
    (hP : _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ P.source)
    (hQ : _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ Q.source)
    (hzero : ∀ z : S2, Q (z,0) = P (η z,1))
    (hmeet : P '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∩ Q '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) =
      P '' (_root_.Set.univ ×ˢ ({1} : Set ℝ))) :
    ∃ R : PartialDiffeomorph SphereCylinderModel I SphereCylinder M ∞,
      _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 2 ⊆ R.source ∧
      R '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 2) =
        P '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∪ Q '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∧
      (∀ z : S2, R (z,0) = P (z,0)) ∧ (∀ z : S2, R (z,2) = Q (η.symm z,1)) ∧
      (∀ z : S2, R =ᶠ[𝓝 (z,0)] P) ∧
      ∀ z : S2, R =ᶠ[𝓝 (z,2)] (fun q => Q (η.symm q.1,q.2-1)) := by
  let D := η.symm.prodCongr (Diffeomorph.refl 𝓘(ℝ) ℝ ∞)
  let Q' := D.toPartialDiffeomorph.trans Q
  have hD (q : SphereCylinder) : D q = (η.symm q.1,q.2) := rfl
  have hband : D '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0:ℝ) 1) = _root_.Set.univ ×ˢ _root_.Set.Icc (0:ℝ) 1 := by
    ext q
    constructor
    · rintro ⟨p,hp,rfl⟩
      exact ⟨mem_univ _,hp.2⟩
    · intro hq
      exact ⟨(η q.1,q.2),⟨mem_univ _,hq.2⟩,Prod.ext (η.symm_apply_apply _) rfl⟩
  have hQ's : _root_.Set.univ ×ˢ _root_.Set.Icc (0:ℝ) 1 ⊆ Q'.source := by
    intro q hq
    exact ⟨mem_univ _,hQ ⟨mem_univ _,hq.2⟩⟩
  have hQ'img : Q' '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0:ℝ) 1) = Q '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0:ℝ) 1) := by
    calc
      Q' '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0:ℝ) 1) = Q '' (D '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0:ℝ) 1)) := by
        rw [_root_.Set.image_image]
        rfl
      _ = _ := by rw [hband]
  have hQ'zero (z : S2) : Q' (z,0) = P (z,1) := by
    change Q (η.symm z,0) = _
    rw [hzero,η.apply_symm_apply]
  obtain ⟨R,hs,hi,hl,hu,hgl,hgu⟩ :=
    exists_slab_concatenation_of_eq P Q' hP hQ's hQ'zero (by rw [hQ'img]; exact hmeet)
  exact ⟨R,hs,hi.trans (congrArg (fun U => P '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0:ℝ) 1) ∪ U) hQ'img),
    hl,hu,hgl,hgu⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_slab_concatenation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_slab_concatenation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_slab_concatenation ``Submission.DifferentialGeometry.Topology.Manifold.exists_slab_concatenation

theorem exists_unit_slab_concatenation
    (P Q : PartialDiffeomorph SphereCylinderModel I SphereCylinder M ∞)
    (η : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2)
    (hP : _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ P.source)
    (hQ : _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ Q.source)
    (hzero : ∀ z : S2, Q (z,0) = P (η z,1))
    (hmeet : P '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∩ Q '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) =
      P '' (_root_.Set.univ ×ˢ ({1} : Set ℝ))) :
    ∃ R : PartialDiffeomorph SphereCylinderModel I SphereCylinder M ∞,
      _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ R.source ∧
      R '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) =
        P '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∪ Q '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∧
      (∀ z : S2, R (z,0) = P (z,0)) ∧ (∀ z : S2, R (z,1) = Q (η.symm z,1)) ∧
      (∀ z : S2, R =ᶠ[𝓝 (z,0)] (fun q => P (q.1,2*q.2))) ∧
      ∀ z : S2, R =ᶠ[𝓝 (z,1)] (fun q => Q (η.symm q.1,2*q.2-1)) := by
  obtain ⟨R,hs,hi,hl,hu,hgl,hgu⟩ := exists_slab_concatenation P Q η hP hQ hzero hmeet
  let D : SphereCylinder ≃ₘ⟮SphereCylinderModel,SphereCylinderModel⟯ SphereCylinder :=
    Diffeomorph.fiberwiseAffine (fun _ => (0:ℝ)) (fun _ => (2:ℝ))
      contMDiff_const contMDiff_const (fun _ => by norm_num)
  have hD (q : SphereCylinder) : D q = (q.1,2*q.2) := by
    change (q.1,0+2*q.2) = _
    rw [zero_add]
  let R' := D.toPartialDiffeomorph.trans R
  have hband : D '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0:ℝ) 1) = _root_.Set.univ ×ˢ _root_.Set.Icc (0:ℝ) 2 := by
    ext q
    constructor
    · rintro ⟨p,hp,rfl⟩
      rw [hD]
      exact ⟨mem_univ _,by linarith [hp.2.1],by linarith [hp.2.2]⟩
    · intro hq
      refine ⟨(q.1,q.2/2),⟨mem_univ _,by linarith [hq.2.1],by linarith [hq.2.2]⟩,?_⟩
      rw [hD]
      apply Prod.ext
      · rfl
      · dsimp
        ring
  have hsrc : _root_.Set.univ ×ˢ _root_.Set.Icc (0:ℝ) 1 ⊆ R'.source := by
    intro q hq
    exact ⟨mem_univ _,hs (hband ▸ _root_.Set.mem_image_of_mem D hq)⟩
  have himg : R' '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0:ℝ) 1) = R '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0:ℝ) 2) := by
    calc
      _ = R '' (D '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0:ℝ) 1)) := by rw [_root_.Set.image_image]; rfl
      _ = _ := by rw [hband]
  refine ⟨R',hsrc,himg.trans hi,?_,?_,?_,?_⟩
  · intro z
    change R (D (z,0)) = _
    rw [hD,_root_.MulZeroClass.mul_zero,hl]
  · intro z
    change R (D (z,1)) = _
    rw [hD,mul_one,hu]
  · intro z
    have ht : _root_.Filter.Tendsto D (𝓝 (z,0)) (𝓝 (z,0)) := by
      simpa only [hD,_root_.MulZeroClass.mul_zero] using D.continuous.continuousAt.tendsto (x := (z,(0:ℝ)))
    have hh := (hgl z).comp_tendsto ht
    filter_upwards [hh] with q hq
    change R (D q) = _
    exact hq.trans (congrArg P (hD q))
  · intro z
    have ht : _root_.Filter.Tendsto D (𝓝 (z,1)) (𝓝 (z,2)) := by
      simpa only [hD,mul_one] using D.continuous.continuousAt.tendsto (x := (z,(1:ℝ)))
    have hh := (hgu z).comp_tendsto ht
    filter_upwards [hh] with q hq
    change R (D q) = _
    change R (D q) = Q (η.symm (D q).1,(D q).2-1) at hq
    exact hq.trans (congrArg Q (by rw [hD]))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_unit_slab_concatenation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_unit_slab_concatenation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_unit_slab_concatenation ``Submission.DifferentialGeometry.Topology.Manifold.exists_unit_slab_concatenation

def cylinderSeamTransport (η : ℕ → S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) :
    ℕ → S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2
  | 0 => Diffeomorph.refl (𝓡 2) S2 ∞
  | n + 1 => (cylinderSeamTransport η n).trans (η n).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.cylinderSeamTransport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.cylinderSeamTransport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.cylinderSeamTransport ``Submission.DifferentialGeometry.Topology.Manifold.cylinderSeamTransport

theorem exists_finite_unit_slab_concatenation
    (P : ℕ → PartialDiffeomorph SphereCylinderModel I SphereCylinder M ∞)
    (η : ℕ → S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) (n : ℕ)
    (hsource : ∀ k ≤ n, _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ (P k).source)
    (hseam : ∀ k < n, ∀ z : S2, P (k + 1) (z, 0) = P k (η k z, 1))
    (hmeet : ∀ k < n,
      (⋃ j ≤ k, P j '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) ∩
          P (k + 1) '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) =
        P k '' (_root_.Set.univ ×ˢ ({1} : Set ℝ))) :
    ∃ R : PartialDiffeomorph SphereCylinderModel I SphereCylinder M ∞,
      _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ R.source ∧
      R '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) = ⋃ k ≤ n, P k '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∧
      (∀ z : S2, R (z, 0) = P 0 (z, 0)) ∧
      ∀ z : S2, R (z, 1) = P n (cylinderSeamTransport η n z, 1) := by
  induction n with
  | zero =>
    refine ⟨P 0, hsource 0 le_rfl, ?_, ?_, ?_⟩
    · simp
    · intro z
      rfl
    · intro z
      rfl
  | succ n ih =>
    obtain ⟨R, hR, himage, hzero, hone⟩ := ih
      (fun k hk => hsource k (hk.trans (Nat.le_succ n)))
      (fun k hk => hseam k (hk.trans (Nat.lt_succ_self n)))
      (fun k hk => hmeet k (hk.trans (Nat.lt_succ_self n)))
    let ρ := cylinderSeamTransport η n
    let κ := (η n).trans ρ.symm
    have hmatch (z : S2) : P (n + 1) (z, 0) = R (κ z, 1) := by
      rw [hone]
      change P (n + 1) (z, 0) = P n (ρ (ρ.symm (η n z)), 1)
      rw [ρ.apply_symm_apply]
      exact hseam n (Nat.lt_succ_self n) z
    have hupper : R '' (_root_.Set.univ ×ˢ ({1} : Set ℝ)) = P n '' (_root_.Set.univ ×ˢ ({1} : Set ℝ)) := by
      ext x
      constructor
      · rintro ⟨⟨z, t⟩, ⟨_, ht⟩, hx⟩
        have ht : t = 1 := ht
        subst t
        exact ⟨(ρ z, 1), ⟨mem_univ _, rfl⟩, (hone z).symm.trans hx⟩
      · rintro ⟨⟨z, t⟩, ⟨_, ht⟩, hx⟩
        have ht : t = 1 := ht
        subst t
        refine ⟨(ρ.symm z, 1), ⟨mem_univ _, rfl⟩, ?_⟩
        rw [hone, ρ.apply_symm_apply]
        exact hx
    have hintersection : R '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∩
        P (n + 1) '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) = R '' (_root_.Set.univ ×ˢ ({1} : Set ℝ)) := by
      rw [himage, hupper]
      exact hmeet n (Nat.lt_succ_self n)
    obtain ⟨R', hR', himage', hzero', hone', _, _⟩ :=
      exists_unit_slab_concatenation R (P (n + 1)) κ hR (hsource _ le_rfl)
        hmatch hintersection
    refine ⟨R', hR', ?_, (fun z => (hzero' z).trans (hzero z)), ?_⟩
    · rw [himage', himage]
      ext x
      simp only [_root_.Set.mem_union, _root_.Set.mem_iUnion]
      constructor
      · rintro (⟨k, hk, hx⟩ | hx)
        · exact ⟨k, hk.trans (Nat.le_succ n), hx⟩
        · exact ⟨n + 1, le_rfl, hx⟩
      · rintro ⟨k, hk, hx⟩
        rcases Nat.eq_or_lt_of_le hk with rfl | hk
        · exact Or.inr hx
        · exact Or.inl ⟨k, Nat.le_of_lt_succ hk, hx⟩
    · intro z
      exact hone' z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_finite_unit_slab_concatenation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_finite_unit_slab_concatenation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_finite_unit_slab_concatenation ``Submission.DifferentialGeometry.Topology.Manifold.exists_finite_unit_slab_concatenation

end DifferentialGeometry.Topology.Manifold
