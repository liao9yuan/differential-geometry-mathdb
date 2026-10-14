import Mathlib.Analysis.Calculus.FDeriv.Extend

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Filter
open scoped _root_.Topology

namespace DifferentialGeometry.Analysis.Calculus.SmoothExtension

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem hasDerivWithinAt_Ici_of_tendsto_nhdsGT
    {f f' : ℝ → F} {L : F} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn f (_root_.Set.Icc a b))
    (hderiv : ∀ x ∈ _root_.Set.Ioo a b, HasDerivAt f (f' x) x)
    (hlim : _root_.Filter.Tendsto f' (𝓝[>] a) (𝓝 L)) :
    HasDerivWithinAt f L (_root_.Set.Ici a) a := by
  refine hasDerivWithinAt_Ici_of_tendsto_deriv
    (fun x hx => (hderiv x hx).differentiableAt.differentiableWithinAt)
    ((hcont a ⟨le_rfl, hab.le⟩).mono _root_.Set.Ioo_subset_Icc_self) (Ioo_mem_nhdsGT hab) ?_
  exact hlim.congr' (Filter.eventuallyEq_of_mem (Ioo_mem_nhdsGT hab)
    (fun x hx => (hderiv x hx).deriv.symm))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Calculus.SmoothExtension.hasDerivWithinAt_Ici_of_tendsto_nhdsGT then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Calculus.SmoothExtension.hasDerivWithinAt_Ici_of_tendsto_nhdsGT"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Calculus.SmoothExtension.hasDerivWithinAt_Ici_of_tendsto_nhdsGT ``Submission.DifferentialGeometry.Analysis.Calculus.SmoothExtension.hasDerivWithinAt_Ici_of_tendsto_nhdsGT

theorem hasDerivWithinAt_Iic_of_tendsto_nhdsLT
    {f f' : ℝ → F} {L : F} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn f (_root_.Set.Icc a b))
    (hderiv : ∀ x ∈ _root_.Set.Ioo a b, HasDerivAt f (f' x) x)
    (hlim : _root_.Filter.Tendsto f' (𝓝[<] b) (𝓝 L)) :
    HasDerivWithinAt f L (_root_.Set.Iic b) b := by
  refine hasDerivWithinAt_Iic_of_tendsto_deriv
    (fun x hx => (hderiv x hx).differentiableAt.differentiableWithinAt)
    ((hcont b ⟨hab.le, le_rfl⟩).mono _root_.Set.Ioo_subset_Icc_self) (Ioo_mem_nhdsLT hab) ?_
  exact hlim.congr' (Filter.eventuallyEq_of_mem (Ioo_mem_nhdsLT hab)
    (fun x hx => (hderiv x hx).deriv.symm))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Calculus.SmoothExtension.hasDerivWithinAt_Iic_of_tendsto_nhdsLT then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Calculus.SmoothExtension.hasDerivWithinAt_Iic_of_tendsto_nhdsLT"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Calculus.SmoothExtension.hasDerivWithinAt_Iic_of_tendsto_nhdsLT ``Submission.DifferentialGeometry.Analysis.Calculus.SmoothExtension.hasDerivWithinAt_Iic_of_tendsto_nhdsLT

theorem hasDerivWithinAt_Icc_of_hasDerivAt_Ioo
    {f f' : ℝ → F} {a b t : ℝ}
    (hf : ContinuousOn f (_root_.Set.Icc a b)) (hf' : ContinuousOn f' (_root_.Set.Icc a b))
    (hderiv : ∀ x ∈ _root_.Set.Ioo a b, HasDerivAt f (f' x) x) (ht : t ∈ _root_.Set.Icc a b) :
    HasDerivWithinAt f (f' t) (_root_.Set.Icc a b) t := by
  rcases lt_trichotomy a b with hab | rfl | hab
  · by_cases hta : t = a
    · subst t
      have hlim : _root_.Filter.Tendsto f' (𝓝[>] a) (𝓝 (f' a)) := by
        rw [← nhdsWithin_Ioo_eq_nhdsGT hab]
        exact (hf' a ⟨le_rfl, hab.le⟩).mono _root_.Set.Ioo_subset_Icc_self
      exact (hasDerivWithinAt_Ici_of_tendsto_nhdsGT hab hf hderiv hlim).mono
        _root_.Set.Icc_subset_Ici_self
    by_cases htb : t = b
    · subst t
      have hlim : _root_.Filter.Tendsto f' (𝓝[<] b) (𝓝 (f' b)) := by
        rw [← nhdsWithin_Ioo_eq_nhdsLT hab]
        exact (hf' b ⟨hab.le, le_rfl⟩).mono _root_.Set.Ioo_subset_Icc_self
      exact (hasDerivWithinAt_Iic_of_tendsto_nhdsLT hab hf hderiv hlim).mono
        _root_.Set.Icc_subset_Iic_self
    exact (hderiv t ⟨lt_of_le_of_ne ht.1 (Ne.symm hta),
      lt_of_le_of_ne ht.2 htb⟩).hasDerivWithinAt
  · rw [_root_.Set.Icc_self, hasDerivWithinAt_iff_hasFDerivWithinAt]
    exact HasFDerivWithinAt.singleton
  · exact (not_le_of_gt hab (ht.1.trans ht.2)).elim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Calculus.SmoothExtension.hasDerivWithinAt_Icc_of_hasDerivAt_Ioo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Calculus.SmoothExtension.hasDerivWithinAt_Icc_of_hasDerivAt_Ioo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Calculus.SmoothExtension.hasDerivWithinAt_Icc_of_hasDerivAt_Ioo ``Submission.DifferentialGeometry.Analysis.Calculus.SmoothExtension.hasDerivWithinAt_Icc_of_hasDerivAt_Ioo

theorem hasDerivAt_ite_of_one_sided_derivatives
    {fL fR : ℝ → F} {s : ℝ} {L : F}
    (hval : fL s = fR s)
    (hL : HasDerivWithinAt fL L (_root_.Set.Iic s) s)
    (hR : HasDerivWithinAt fR L (_root_.Set.Ici s) s) :
    HasDerivAt (fun t => if t ≤ s then fL t else fR t) L s := by
  have hL' : HasDerivWithinAt (fun t => if t ≤ s then fL t else fR t) L (_root_.Set.Iic s) s :=
    hL.congr (fun t ht => if_pos ht) (if_pos le_rfl)
  have hR' : HasDerivWithinAt (fun t => if t ≤ s then fL t else fR t) L (_root_.Set.Ici s) s := by
    apply hR.congr
    · intro t ht
      rcases eq_or_lt_of_le (mem_Ici.mp ht) with rfl | hst
      · exact (if_pos le_rfl).trans hval
      · exact if_neg (not_le.mpr hst)
    · exact (if_pos le_rfl).trans hval
  simpa only [_root_.Set.Iic_union_Ici, hasDerivWithinAt_univ] using hL'.union hR'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Calculus.SmoothExtension.hasDerivAt_ite_of_one_sided_derivatives then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Calculus.SmoothExtension.hasDerivAt_ite_of_one_sided_derivatives"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Calculus.SmoothExtension.hasDerivAt_ite_of_one_sided_derivatives ``Submission.DifferentialGeometry.Analysis.Calculus.SmoothExtension.hasDerivAt_ite_of_one_sided_derivatives

theorem hasDerivAt_ite_of_tendsto_derivatives
    {fL fR FL FR : ℝ → F} {a s b : ℝ} {L : F} (ha : a < s) (hb : s < b)
    (hL : ContinuousWithinAt fL (_root_.Set.Icc a s) s)
    (hR : ContinuousWithinAt fR (_root_.Set.Icc s b) s)
    (hderivL : ∀ t ∈ _root_.Set.Ioo a s, HasDerivAt fL (FL t) t)
    (hderivR : ∀ t ∈ _root_.Set.Ioo s b, HasDerivAt fR (FR t) t)
    (hval : fL s = fR s)
    (hlimL : _root_.Filter.Tendsto FL (𝓝[<] s) (𝓝 L))
    (hlimR : _root_.Filter.Tendsto FR (𝓝[>] s) (𝓝 L)) :
    HasDerivAt (fun t => if t ≤ s then fL t else fR t) L s := by
  apply hasDerivAt_ite_of_one_sided_derivatives hval
  · refine hasDerivWithinAt_Iic_of_tendsto_deriv
      (fun t ht => (hderivL t ht).differentiableAt.differentiableWithinAt)
      (hL.mono _root_.Set.Ioo_subset_Icc_self) (Ioo_mem_nhdsLT ha) ?_
    exact hlimL.congr' (Filter.eventuallyEq_of_mem (Ioo_mem_nhdsLT ha)
      (fun t ht => (hderivL t ht).deriv.symm))
  · refine hasDerivWithinAt_Ici_of_tendsto_deriv
      (fun t ht => (hderivR t ht).differentiableAt.differentiableWithinAt)
      (hR.mono _root_.Set.Ioo_subset_Icc_self) (Ioo_mem_nhdsGT hb) ?_
    exact hlimR.congr' (Filter.eventuallyEq_of_mem (Ioo_mem_nhdsGT hb)
      (fun t ht => (hderivR t ht).deriv.symm))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Calculus.SmoothExtension.hasDerivAt_ite_of_tendsto_derivatives then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Calculus.SmoothExtension.hasDerivAt_ite_of_tendsto_derivatives"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Calculus.SmoothExtension.hasDerivAt_ite_of_tendsto_derivatives ``Submission.DifferentialGeometry.Analysis.Calculus.SmoothExtension.hasDerivAt_ite_of_tendsto_derivatives

theorem hasDerivAt_ite_of_continuous_derivatives
    {fL fR FL FR : ℝ → F} {a s b : ℝ} (ha : a < s) (hb : s < b)
    (hL : ContinuousWithinAt fL (_root_.Set.Icc a s) s)
    (hR : ContinuousWithinAt fR (_root_.Set.Icc s b) s)
    (hderivL : ∀ t ∈ _root_.Set.Ioo a s, HasDerivAt fL (FL t) t)
    (hderivR : ∀ t ∈ _root_.Set.Ioo s b, HasDerivAt fR (FR t) t)
    (hval : fL s = fR s)
    (hFL : ContinuousWithinAt FL (_root_.Set.Icc a s) s)
    (hFR : ContinuousWithinAt FR (_root_.Set.Icc s b) s) (hmatch : FL s = FR s) :
    HasDerivAt (fun t => if t ≤ s then fL t else fR t) (FL s) s := by
  apply hasDerivAt_ite_of_tendsto_derivatives ha hb hL hR hderivL hderivR hval
  · rw [← nhdsWithin_Ioo_eq_nhdsLT ha]
    exact hFL.mono _root_.Set.Ioo_subset_Icc_self
  · rw [hmatch, ← nhdsWithin_Ioo_eq_nhdsGT hb]
    exact hFR.mono _root_.Set.Ioo_subset_Icc_self

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Calculus.SmoothExtension.hasDerivAt_ite_of_continuous_derivatives then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Calculus.SmoothExtension.hasDerivAt_ite_of_continuous_derivatives"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Calculus.SmoothExtension.hasDerivAt_ite_of_continuous_derivatives ``Submission.DifferentialGeometry.Analysis.Calculus.SmoothExtension.hasDerivAt_ite_of_continuous_derivatives

end DifferentialGeometry.Analysis.Calculus.SmoothExtension
