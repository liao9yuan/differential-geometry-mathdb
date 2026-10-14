import Submission.DifferentialGeometry.Analysis.Calculus.Inverse.LocalInverse

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Filter _root_.Topology
open scoped _root_.ContDiff

namespace DifferentialGeometry.Analysis

variable {P E : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_localInverse_preserving_vector_parameter
    {h : P × E → E} {U : Set (P × E)} {q : P × E}
    (hh : ContDiffOn ℝ ∞ h U) (hU : IsOpen U) (hq : q ∈ U)
    (A : E ≃L[ℝ] E)
    (hvertical : ∀ w, fderiv ℝ h q (0, w) = A w) :
    ∃ e : OpenPartialHomeomorph (P × E) (P × E),
      q ∈ e.source ∧ e.source ⊆ U ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ r, e r = (r.1, h r)) ∧
      ∀ r ∈ e.target, (e.symm r).1 = r.1 ∧ h (e.symm r) = r.2 := by
  let L := fderiv ℝ h q
  let T : (P × E) ≃L[ℝ] (P × E) := (ContinuousLinearEquiv.refl ℝ P).skewProd A
    (L.comp (ContinuousLinearMap.inl ℝ P E))
  have hT : (T : (P × E) →L[ℝ] (P × E)) = (ContinuousLinearMap.fst ℝ P E).prod L := by
    apply ContinuousLinearMap.ext
    intro r
    change (r.1, A r.2 + L (r.1, 0)) = (r.1, L r)
    refine Prod.ext rfl ?_
    have hr : r = (r.1, (0 : E)) + ((0 : P), r.2) := by simp
    have hLr : L r = L (r.1, 0) + A r.2 := by
      conv_lhs => rw [hr]
      rw [map_add, hvertical]
    rw [hLr, add_comm]
  have hd : HasFDerivAt (fun r : P × E ↦ (r.1, h r))
      (T : (P × E) →L[ℝ] (P × E)) q := by
    rw [hT]
    exact hasFDerivAt_fst.prodMk
      ((hh.contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp)).hasFDerivAt
  obtain ⟨e, heq, heU, he, hei, hemap⟩ :=
    exists_localInverse_of_hasFDerivAt_equiv (contDiffOn_fst.prodMk hh) hU hq hd
  refine ⟨e, heq, heU, he, hei, hemap, ?_⟩
  intro r hr
  exact Prod.mk.inj ((hemap _).symm.trans (e.right_inv hr))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_localInverse_preserving_vector_parameter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_localInverse_preserving_vector_parameter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_localInverse_preserving_vector_parameter ``Submission.DifferentialGeometry.Analysis.exists_localInverse_preserving_vector_parameter

theorem exists_contDiffOn_vector_inverse_of_bijective
    {h : P × E → E} {V : Set P} (hV : IsOpen V)
    (hh : ContDiffOn ℝ ∞ h (V ×ˢ _root_.Set.univ))
    (hbij : ∀ p ∈ V, Function.Bijective (fun x ↦ h (p, x)))
    (hvertical : ∀ p ∈ V, ∀ x, ∃ A : E ≃L[ℝ] E,
      ∀ w, fderiv ℝ h (p, x) (0, w) = A w) :
    ∃ R : P × E → E, ContDiffOn ℝ ∞ R (V ×ˢ _root_.Set.univ) ∧
      (∀ p ∈ V, ∀ x, R (p, h (p, x)) = x) ∧
      ∀ p ∈ V, ∀ y, h (p, R (p, y)) = y := by
  let R : P × E → E := fun q ↦ Function.invFun (fun x ↦ h (q.1, x)) q.2
  have hleft (p : P) (hp : p ∈ V) (x : E) : R (p, h (p, x)) = x :=
    Function.leftInverse_invFun (hbij p hp).1 x
  have hright (p : P) (hp : p ∈ V) (y : E) : h (p, R (p, y)) = y :=
    Function.rightInverse_invFun (hbij p hp).2 y
  refine ⟨R, ?_, hleft, hright⟩
  intro q hq
  obtain ⟨A, hA⟩ := hvertical q.1 hq.1 (R q)
  obtain ⟨e, hp, _, _, hei, he, hparam⟩ :=
    exists_localInverse_preserving_vector_parameter hh (hV.prod isOpen_univ)
      (show (q.1, R q) ∈ V ×ˢ _root_.Set.univ from ⟨hq.1, _root_.Set.mem_univ _⟩) A hA
  have heq : e (q.1, R q) = q := by rw [he, hright q.1 hq.1]
  have ht : q ∈ e.target := heq ▸ e.map_source hp
  have hagree : R =ᶠ[𝓝[V ×ˢ _root_.Set.univ] q] fun r ↦ (e.symm r).2 := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (e.open_target.mem_nhds ht), self_mem_nhdsWithin]
      with r hr hrV
    apply (hbij r.1 hrV.1).1
    change h (r.1, R (r.1, r.2)) = h (r.1, (e.symm r).2)
    rw [hright r.1 hrV.1]
    have hp := hparam r hr
    have hr' : (r.1, (e.symm r).2) = e.symm r := Prod.ext hp.1.symm rfl
    exact ((congrArg h hr').trans hp.2).symm
  exact ((hei.contDiffAt (e.open_target.mem_nhds ht)).snd).contDiffWithinAt.congr_of_eventuallyEq
    hagree (hagree.eq_of_nhdsWithin hq)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_contDiffOn_vector_inverse_of_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_contDiffOn_vector_inverse_of_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_contDiffOn_vector_inverse_of_bijective ``Submission.DifferentialGeometry.Analysis.exists_contDiffOn_vector_inverse_of_bijective

end DifferentialGeometry.Analysis
