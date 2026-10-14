import Submission.DifferentialGeometry.Topology.Manifold.CylinderCollar.CoorientedExtension
import Submission.DifferentialGeometry.Topology.Manifold.SphereDegreeReflection
import Submission.DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import Submission.DifferentialGeometry.Topology.Manifold.OpenEmbedding
import Submission.DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph
import Submission.DifferentialGeometry.Topology.Manifold.SmoothEmbeddingFromOpen

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.Manifold

private abbrev S2 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.S2 target :: scope.openDecls } }

theorem exists_signed_supported_collar_matching_of_sphere
    (φ : PartialDiffeomorph SphereCylinderModel SphereCylinderModel SphereCylinder SphereCylinder ∞)
    (F₀ : SphereCylinder ≃ₘ⟮SphereCylinderModel, SphereCylinderModel⟯ SphereCylinder)
    (η : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) (hη : sphereDiffeomorphDegree η = 1)
    {r R ρ a : ℝ} (hr : 0 < r) (hrR : r < R) (hρa : ρ + R < a)
    (hsource : _root_.Set.univ ×ˢ _root_.Set.Icc (-R) R ⊆ φ.source)
    (hzero : ∀ p : S2, F₀ (η p,a) = φ (p,0))
    (hdepth : ∀ q ∈ _root_.Set.univ ×ˢ _root_.Set.Icc (-R) R, ρ < (φ q).2)
    (K₀ : Set SphereCylinder) (hK₀ : IsCompact K₀) (hK₀ρ : K₀ ⊆ _root_.Set.univ ×ˢ _root_.Set.Ioi ρ)
    (hfix₀ : _root_.Set.EqOn F₀ id K₀ᶜ) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      ∃ F : SphereCylinder ≃ₘ⟮SphereCylinderModel, SphereCylinderModel⟯ SphereCylinder,
        (∀ q : SphereCylinder, |q.2| ≤ r → F (q.1,a + q.2) = φ (q.1,σ * q.2)) ∧
        ∃ K : Set SphereCylinder, IsCompact K ∧ K ⊆ _root_.Set.univ ×ˢ _root_.Set.Ioi ρ ∧
          EqOn F id Kᶜ ∧ _root_.Set.EqOn F.symm id Kᶜ := by
  let T := DifferentialGeometry.Geometry.Metric.cylinderAxialDiffeomorph (I := 𝓡 2) (M := S2) a 1 (by norm_num)
  let A := (φ.trans F₀.symm.toPartialDiffeomorph).trans T.symm.toPartialDiffeomorph
  have hAs : _root_.Set.univ ×ˢ _root_.Set.Icc (-R) R ⊆ A.source :=
    fun q hq => ⟨⟨hsource hq,_root_.Set.mem_univ _⟩,_root_.Set.mem_univ _⟩
  have hAq (q : SphereCylinder) : A q = ((F₀.symm (φ q)).1,(F₀.symm (φ q)).2-a) := by
    change ((F₀.symm (φ q)).1,1 * ((F₀.symm (φ q)).2-a)) = _
    rw [one_mul]
  have hA0 (p : S2) : A (p,0) = (η p,0) := by
    rw [hAq,← hzero,F₀.symm_apply_apply,sub_self]
  have hlow (q : SphereCylinder) (hq : q ∈ _root_.Set.univ ×ˢ _root_.Set.Icc (-R) R) : ρ-a < (A q).2 := by
    have hFi : ρ < (F₀.symm (φ q)).2 := by
      by_contra hn
      have hh : F₀.symm (φ q) ∉ K₀ := fun hm => (not_lt_of_ge (le_of_not_gt hn)) (hK₀ρ hm).2
      have h := hfix₀ hh
      have heq : F₀.symm (φ q) = φ q := h.symm.trans (F₀.apply_symm_apply _)
      rw [heq] at hn
      exact hn (hdepth q hq)
    rw [hAq]
    exact sub_lt_sub_right hFi a
  have hAc : IsCompact (A '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-R) R)) :=
    (isCompact_univ.prod _root_.CompactIccSpace.isCompact_Icc).image_of_continuousOn (A.contMDiffOn_toFun.continuousOn.mono hAs)
  obtain ⟨C,hC⟩ := hAc.bddAbove_image continuous_snd.continuousOn
  let u := _root_.Max.max C R + 1
  have hAu : A '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-R) R) ⊆ _root_.Set.univ ×ˢ _root_.Set.Ioo (ρ-a) u := by
    rintro q ⟨z,hz,rfl⟩
    refine ⟨mem_univ _,hlow z hz,?_⟩
    have hh := hC (_root_.Set.mem_image_of_mem Prod.snd (_root_.Set.mem_image_of_mem A hz))
    exact hh.trans_lt (lt_of_le_of_lt (le_max_left C R) (lt_add_one _))
  obtain ⟨σ,hσ,G,hG,hG0,K,hK,hKU,hfix,hfixi⟩ :=
    exists_signed_supported_compact_collar_extension A η hη hr hrR
      (by linarith) (lt_of_le_of_lt (le_max_right C R) (lt_add_one _)) hAs hA0 hAu
  let F := ((T.symm.trans G).trans T).trans F₀
  have hF (q : SphereCylinder) (hq : |q.2| ≤ r) : F (q.1,a+q.2) = φ (q.1,σ*q.2) := by
    have hTq : T.symm (q.1,a+q.2) = q := by
      change (q.1,1 * (a+q.2-a)) = q
      simp only [one_mul,add_sub_cancel_left,Prod.mk.eta]
    change F₀ (T (G (T.symm (q.1,a+q.2)))) = _
    rw [hTq,hG q hq]
    change F₀ (T (T.symm (F₀.symm (φ (q.1,σ*q.2))))) = _
    rw [T.apply_symm_apply,F₀.apply_symm_apply]
  have hKT : T '' K ⊆ _root_.Set.univ ×ˢ _root_.Set.Ioi ρ := by
    rintro q ⟨z,hz,rfl⟩
    refine ⟨mem_univ _,?_⟩
    change ρ < a+1*z.2
    have hh := (hKU hz).2.1
    linarith
  have hFfix (q : SphereCylinder) (hq : q ∉ K₀ ∪ T '' K) : F q = q := by
    have hn₀ : q ∉ K₀ := fun h => hq (Or.inl h)
    have hnK : T.symm q ∉ K := fun h => hq (Or.inr ⟨T.symm q,h,T.apply_symm_apply q⟩)
    change F₀ (T (G (T.symm q))) = q
    rw [hfix hnK,id_eq,T.apply_symm_apply,hfix₀ hn₀]
    rfl
  refine ⟨σ,hσ,F,hF,K₀ ∪ T '' K,hK₀.union (hK.image T.continuous),_root_.Set.union_subset hK₀ρ hKT,hFfix,?_⟩
  intro q hq
  apply F.injective
  exact (F.apply_symm_apply q).trans (hFfix q hq).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_signed_supported_collar_matching_of_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_signed_supported_collar_matching_of_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_signed_supported_collar_matching_of_sphere ``Submission.DifferentialGeometry.Topology.Manifold.exists_signed_supported_collar_matching_of_sphere


private theorem exists_partialDiffeomorph_of_open_cylinder_embedding
    (U : TopologicalSpace.Opens SphereCylinder) (x₀ : U)
    (f : U → SphereCylinder) (hf : _root_.Manifold.IsSmoothEmbedding SphereCylinderModel SphereCylinderModel ∞ f) :
    ∃ φ : PartialDiffeomorph SphereCylinderModel SphereCylinderModel SphereCylinder SphereCylinder ∞,
      φ.source = U ∧ φ.target = _root_.Set.range f ∧ ∀ q : U, φ q.val = f q := by
  have hlocal : IsLocalDiffeomorph SphereCylinderModel SphereCylinderModel ∞ f :=
    isLocalDiffeomorph_of_injective_mfderiv f hf.contMDiff
      (fun q => (hf.isImmersion.isImmersionAt q).injective_mfderiv (by simp)) rfl
  let V := hlocal.image
  let e := diffeomorphOntoImage f hlocal hf.isEmbedding.injective
  let iU := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph SphereCylinderModel U ⟨x₀⟩
  let iV := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph SphereCylinderModel V ⟨e x₀⟩
  let φ := (iU.symm.trans e.toPartialDiffeomorph).trans iV
  have hiU : iU.target = (U : Set SphereCylinder) :=
    DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target _ _ _
  have hiV : iV.target = (V : Set SphereCylinder) :=
    DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target _ _ _
  refine ⟨φ,?_,?_,?_⟩
  · ext q
    change ((q ∈ iU.target ∧ iU.symm q ∈ (_root_.Set.univ : Set U)) ∧ e (iU.symm q) ∈ (_root_.Set.univ : Set V)) ↔ q ∈ U
    simp only [_root_.Set.mem_univ,and_true,hiU]
    rfl
  · ext q
    change (q ∈ iV.target ∧ (iV.symm q ∈ (_root_.Set.univ : Set V) ∧ e.symm (iV.symm q) ∈ (_root_.Set.univ : Set U))) ↔ q ∈ _root_.Set.range f
    simp only [_root_.Set.mem_univ,and_self,and_true,hiV]
    rfl
  · intro q
    have hq := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_symm_apply SphereCylinderModel U ⟨x₀⟩ q.property
    change (e (iU.symm q.val)).val = f q
    rw [hq]
    rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.exists_partialDiffeomorph_of_open_cylinder_embedding
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.exists_partialDiffeomorph_of_open_cylinder_embedding target :: scope.openDecls } }


theorem exists_reflected_supported_collar_matching_of_sphere
    (φ : PartialDiffeomorph SphereCylinderModel SphereCylinderModel SphereCylinder SphereCylinder ∞)
    (F₀ : SphereCylinder ≃ₘ⟮SphereCylinderModel, SphereCylinderModel⟯ SphereCylinder)
    (η : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2)
    {r R ρ a : ℝ} (hr : 0 < r) (hrR : r < R) (hρa : ρ + R < a)
    (hsource : _root_.Set.univ ×ˢ _root_.Set.Icc (-R) R ⊆ φ.source)
    (hzero : ∀ p : S2, F₀ (η p,a) = φ (p,0))
    (hdepth : ∀ q ∈ _root_.Set.univ ×ˢ _root_.Set.Icc (-R) R, ρ < (φ q).2)
    (K₀ : Set SphereCylinder) (hK₀ : IsCompact K₀) (hK₀ρ : K₀ ⊆ _root_.Set.univ ×ˢ _root_.Set.Ioi ρ)
    (hfix₀ : _root_.Set.EqOn F₀ id K₀ᶜ) :
    ∃ (β : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) (σ : ℝ),
      (β = Diffeomorph.refl (𝓡 2) S2 ∞ ∨ β = sphereAntipodalDiffeomorph (n := 2)) ∧
      (σ = 1 ∨ σ = -1) ∧
      ∃ F : SphereCylinder ≃ₘ⟮SphereCylinderModel, SphereCylinderModel⟯ SphereCylinder,
        (∀ q : SphereCylinder, |q.2| ≤ r → F (q.1,a + q.2) = φ (β q.1,σ * q.2)) ∧
        ∃ K : Set SphereCylinder, IsCompact K ∧ K ⊆ _root_.Set.univ ×ˢ _root_.Set.Ioi ρ ∧
          EqOn F id Kᶜ ∧ _root_.Set.EqOn F.symm id Kᶜ := by
  have hβ : ∃ β : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2,
      (β = Diffeomorph.refl (𝓡 2) S2 ∞ ∨ β = sphereAntipodalDiffeomorph (n := 2)) ∧
      sphereDiffeomorphDegree (β.trans η) = 1 := by
    rcases sphereDiffeomorphDegree_eq_one_or_neg_one η with h | h
    · refine ⟨Diffeomorph.refl (𝓡 2) S2 ∞,Or.inl rfl,?_⟩
      have heq : (Diffeomorph.refl (𝓡 2) S2 ∞).trans η = η := by ext p; rfl
      rw [heq]
      exact h
    · exact ⟨sphereAntipodalDiffeomorph (n := 2),Or.inr rfl,
        sphereDiffeomorphDegree_pre_antipodal_eq_one η h⟩
  obtain ⟨β,hβ,hdeg⟩ := hβ
  let D := β.prodCongr (Diffeomorph.refl 𝓘(ℝ) ℝ ∞)
  let ψ := D.toPartialDiffeomorph.trans φ
  have hs : _root_.Set.univ ×ˢ _root_.Set.Icc (-R) R ⊆ ψ.source :=
    fun q hq => ⟨mem_univ _,hsource ⟨mem_univ _,hq.2⟩⟩
  have hz (p : S2) : F₀ ((β.trans η) p,a) = ψ (p,0) := hzero (β p)
  have hd : ∀ q ∈ _root_.Set.univ ×ˢ _root_.Set.Icc (-R) R, ρ < (ψ q).2 :=
    fun q hq => hdepth (β q.1,q.2) ⟨mem_univ _,hq.2⟩
  obtain ⟨σ,hσ,F,hF,K,hK,hKρ,hfix,hfixi⟩ :=
    exists_signed_supported_collar_matching_of_sphere ψ F₀ (β.trans η) hdeg hr hrR hρa
      hs hz hd K₀ hK₀ hK₀ρ hfix₀
  exact ⟨β,σ,hβ,hσ,F,hF,K,hK,hKρ,hfix,hfixi⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_reflected_supported_collar_matching_of_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_reflected_supported_collar_matching_of_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_reflected_supported_collar_matching_of_sphere ``Submission.DifferentialGeometry.Topology.Manifold.exists_reflected_supported_collar_matching_of_sphere


theorem exists_reflected_supported_collar_matching_of_embedding
    (U : TopologicalSpace.Opens SphereCylinder)
    (f : U → SphereCylinder) (hf : _root_.Manifold.IsSmoothEmbedding SphereCylinderModel SphereCylinderModel ∞ f)
    (F₀ : SphereCylinder ≃ₘ⟮SphereCylinderModel, SphereCylinderModel⟯ SphereCylinder)
    (η : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2)
    {r R ρ a : ℝ} (hr : 0 < r) (hrR : r < R) (hρa : ρ + R < a)
    (hsource : _root_.Set.univ ×ˢ _root_.Set.Icc (-R) R ⊆ (U : Set SphereCylinder))
    (hz : ∀ p : S2, (p,(0 : ℝ)) ∈ (U : Set SphereCylinder))
    (hzero : ∀ p : S2, F₀ (η p,a) = f ⟨(p,0),hz p⟩)
    (hdepth : ∀ q : U, q.val ∈ _root_.Set.univ ×ˢ _root_.Set.Icc (-R) R → ρ < (f q).2)
    (K₀ : Set SphereCylinder) (hK₀ : IsCompact K₀) (hK₀ρ : K₀ ⊆ _root_.Set.univ ×ˢ _root_.Set.Ioi ρ)
    (hfix₀ : _root_.Set.EqOn F₀ id K₀ᶜ) :
    ∃ (β : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) (σ : ℝ),
      (β = Diffeomorph.refl (𝓡 2) S2 ∞ ∨ β = sphereAntipodalDiffeomorph (n := 2)) ∧
      (σ = 1 ∨ σ = -1) ∧
      ∃ F : SphereCylinder ≃ₘ⟮SphereCylinderModel, SphereCylinderModel⟯ SphereCylinder,
        (∀ q : SphereCylinder, |q.2| ≤ r →
          ∃ hq : (β q.1,σ*q.2) ∈ U, F (q.1,a+q.2) = f ⟨(β q.1,σ*q.2),hq⟩) ∧
        ∃ K : Set SphereCylinder, IsCompact K ∧ K ⊆ _root_.Set.univ ×ˢ _root_.Set.Ioi ρ ∧
          EqOn F id Kᶜ ∧ _root_.Set.EqOn F.symm id Kᶜ := by
  let v : S2 := ⟨EuclideanSpace.single 0 1,by simp⟩
  obtain ⟨φ,hφs,hφt,hφ⟩ := exists_partialDiffeomorph_of_open_cylinder_embedding U ⟨(v,0),hz v⟩ f hf
  have hs : _root_.Set.univ ×ˢ _root_.Set.Icc (-R) R ⊆ φ.source := hφs.symm ▸ hsource
  have hzero' (p : S2) : F₀ (η p,a) = φ (p,0) := (hzero p).trans (hφ ⟨(p,0),hz p⟩).symm
  have hdepth' : ∀ q ∈ _root_.Set.univ ×ˢ _root_.Set.Icc (-R) R, ρ < (φ q).2 := by
    intro q hq
    rw [hφ ⟨q,hsource hq⟩]
    exact hdepth ⟨q,hsource hq⟩ hq
  obtain ⟨β,σ,hβ,hσ,F,hF,K,hK,hKρ,hfix,hfixi⟩ :=
    exists_reflected_supported_collar_matching_of_sphere φ F₀ η hr hrR hρa hs hzero' hdepth' K₀ hK₀ hK₀ρ hfix₀
  refine ⟨β,σ,hβ,hσ,F,?_,K,hK,hKρ,hfix,hfixi⟩
  intro q hq
  have hσabs : |σ*q.2| = |q.2| := by rcases hσ with h | h <;> simp [h]
  have hqR : (β q.1,σ*q.2) ∈ _root_.Set.univ ×ˢ _root_.Set.Icc (-R) R :=
    ⟨mem_univ _,abs_le.mp (hσabs ▸ hq.trans hrR.le)⟩
  exact ⟨hsource hqR,(hF q hq).trans (hφ ⟨_,hsource hqR⟩)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_reflected_supported_collar_matching_of_embedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_reflected_supported_collar_matching_of_embedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_reflected_supported_collar_matching_of_embedding ``Submission.DifferentialGeometry.Topology.Manifold.exists_reflected_supported_collar_matching_of_embedding


end DifferentialGeometry.Topology.Manifold
