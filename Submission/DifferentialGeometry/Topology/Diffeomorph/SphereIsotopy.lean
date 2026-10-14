import Submission.DifferentialGeometry.Topology.Diffeomorph.Radial
import Mathlib.Logic.Equiv.Prod

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

open scoped _root_.ContDiff _root_.Manifold _root_.Topology

namespace Diffeomorph
open _root_.Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 F H'}
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners 𝕜 G H''}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
  {n : ℕ∞ω}

open _root_.Diffeomorph in
private theorem contMDiff_conjugated_family (c : Diffeomorph I J M N n)
    (f : P → N → N) (hf : ContMDiff (K.prod J) J n (fun z : P × N => f z.1 z.2)) :
    ContMDiff (K.prod I) I n (fun z : P × M => c.symm (f z.1 (c z.2))) := by
  have hc : ContMDiff (K.prod I) (K.prod J) n (Prod.map (id : P → P) c) :=
    (contMDiff_id : ContMDiff K K n (id : P → P)).prodMap c.contMDiff
  exact c.symm.contMDiff.comp (hf.comp hc)

run_cmd do
  let target := ``Submission.Diffeomorph.contMDiff_conjugated_family
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Diffeomorph.contMDiff_conjugated_family target :: scope.openDecls } }

end Diffeomorph

end

section

open scoped _root_.ContDiff _root_.Manifold _root_.Topology

namespace Diffeomorph
open _root_.Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 F H'}
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners 𝕜 G H''}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
  {n : ℕ∞ω}

open _root_.Diffeomorph in
private theorem contMDiff_conjugated_diffeomorph_family (c : Diffeomorph I J M N n)
    (f : P → Diffeomorph J J N N n)
    (hf : ContMDiff (K.prod J) J n (fun z : P × N => f z.1 z.2)) :
    ContMDiff (K.prod I) I n
      (fun z : P × M => ((c.trans (f z.1)).trans c.symm) z.2) :=
  contMDiff_conjugated_family c (fun p => f p) hf

run_cmd do
  let target := ``Submission.Diffeomorph.contMDiff_conjugated_diffeomorph_family
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Diffeomorph.contMDiff_conjugated_diffeomorph_family target :: scope.openDecls } }

open _root_.Diffeomorph in
private theorem contMDiff_conjugated_diffeomorph_family_symm (c : Diffeomorph I J M N n)
    (f : P → Diffeomorph J J N N n)
    (hi : ContMDiff (K.prod J) J n (fun z : P × N => (f z.1).symm z.2)) :
    ContMDiff (K.prod I) I n
      (fun z : P × M => ((c.trans (f z.1)).trans c.symm).symm z.2) :=
  contMDiff_conjugated_family c (fun p => (f p).symm) hi

run_cmd do
  let target := ``Submission.Diffeomorph.contMDiff_conjugated_diffeomorph_family_symm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Diffeomorph.contMDiff_conjugated_diffeomorph_family_symm target :: scope.openDecls } }

end Diffeomorph

end

section

open scoped _root_.ContDiff _root_.Manifold _root_.Topology

namespace Diffeomorph
open _root_.Diffeomorph

open _root_.Diffeomorph in
private noncomputable def sphereIsotopyRadialCutoff (r : ℝ) : ℝ :=
  Real.smoothTransition (4 * r - 1) * Real.smoothTransition (4 - 2 * r)

run_cmd do
  let target := ``Submission.Diffeomorph.sphereIsotopyRadialCutoff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Diffeomorph.sphereIsotopyRadialCutoff target :: scope.openDecls } }

open _root_.Diffeomorph in
private theorem sphereIsotopyRadialCutoff_contDiff :
    ContDiff ℝ ∞ sphereIsotopyRadialCutoff :=
  (Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const)).mul
      (Real.smoothTransition.contDiff.comp
        (contDiff_const.sub (contDiff_const.mul contDiff_id)))

run_cmd do
  let target := ``Submission.Diffeomorph.sphereIsotopyRadialCutoff_contDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Diffeomorph.sphereIsotopyRadialCutoff_contDiff target :: scope.openDecls } }

open _root_.Diffeomorph in
private theorem sphereIsotopyRadialCutoff_zero {r : ℝ}
    (hr : r ≤ 1 / 4 ∨ 2 ≤ r) : sphereIsotopyRadialCutoff r = 0 := by
  rcases hr with hr | hr
  · rw [sphereIsotopyRadialCutoff, Real.smoothTransition.zero_of_nonpos (by linarith),
      _root_.MulZeroClass.zero_mul]
  · rw [sphereIsotopyRadialCutoff,
      Real.smoothTransition.zero_of_nonpos (by linarith : 4 - 2 * r ≤ 0), _root_.MulZeroClass.mul_zero]

run_cmd do
  let target := ``Submission.Diffeomorph.sphereIsotopyRadialCutoff_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Diffeomorph.sphereIsotopyRadialCutoff_zero target :: scope.openDecls } }

open _root_.Diffeomorph in
private theorem sphereIsotopyRadialCutoff_one {r : ℝ}
    (hr : r ∈ Set.Icc (1 / 2 : ℝ) (3 / 2)) : sphereIsotopyRadialCutoff r = 1 := by
  rw [sphereIsotopyRadialCutoff, Real.smoothTransition.one_of_one_le (by linarith [hr.1]),
    Real.smoothTransition.one_of_one_le (by linarith [hr.2]), mul_one]

run_cmd do
  let target := ``Submission.Diffeomorph.sphereIsotopyRadialCutoff_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Diffeomorph.sphereIsotopyRadialCutoff_one target :: scope.openDecls } }

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {d : ℕ} [Fact (Module.finrank ℝ E = d + 1)]

open _root_.Diffeomorph in
private theorem contMDiff_sphereIsotopyAnnulus
    (h : ℝ → Diffeomorph (𝓡 d) (𝓡 d) (Metric.sphere (0 : E) 1)
      (Metric.sphere (0 : E) 1) ∞)
    (hh : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 d)) (𝓡 d) ∞
      (fun z : ℝ × Metric.sphere (0 : E) 1 => h z.1 z.2)) :
    let V : TopologicalSpace.Opens ℝ := ⟨Set.Ioi 0, isOpen_Ioi⟩
    ContMDiff (𝓘(ℝ, ℝ).prod ((𝓡 d).prod 𝓘(ℝ, ℝ)))
      ((𝓡 d).prod 𝓘(ℝ, ℝ)) ∞
      (fun z : ℝ × (Metric.sphere (0 : E) 1 × V) =>
        (h (sphereIsotopyRadialCutoff z.2.2.val * z.1) z.2.1, z.2.2)) := by
  let V : TopologicalSpace.Opens ℝ := ⟨Set.Ioi 0, isOpen_Ioi⟩
  have hr : ContMDiff (𝓘(ℝ, ℝ).prod ((𝓡 d).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × (Metric.sphere (0 : E) 1 × V) => z.2.2.val) :=
    contMDiff_subtype_val.comp contMDiff_snd.snd
  have ht : ContMDiff (𝓘(ℝ, ℝ).prod ((𝓡 d).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × (Metric.sphere (0 : E) 1 × V) =>
        sphereIsotopyRadialCutoff z.2.2.val * z.1) :=
    (contDiff_mul : ContDiff ℝ ∞ (fun z : ℝ × ℝ => z.1 * z.2)).comp_contMDiff
      ((sphereIsotopyRadialCutoff_contDiff.contMDiff.comp hr).prodMk_space contMDiff_fst)
  exact (hh.comp (ht.prodMk contMDiff_snd.fst)).prodMk contMDiff_snd.snd

run_cmd do
  let target := ``Submission.Diffeomorph.contMDiff_sphereIsotopyAnnulus
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Diffeomorph.contMDiff_sphereIsotopyAnnulus target :: scope.openDecls } }

open _root_.Diffeomorph in
private theorem contMDiff_sphereIsotopyAnnulus_fixed_time
    (h : ℝ → Diffeomorph (𝓡 d) (𝓡 d) (Metric.sphere (0 : E) 1)
      (Metric.sphere (0 : E) 1) ∞)
    (hh : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 d)) (𝓡 d) ∞
      (fun z : ℝ × Metric.sphere (0 : E) 1 => h z.1 z.2)) (t : ℝ) :
    let V : TopologicalSpace.Opens ℝ := ⟨Set.Ioi 0, isOpen_Ioi⟩
    ContMDiff ((𝓡 d).prod 𝓘(ℝ, ℝ)) ((𝓡 d).prod 𝓘(ℝ, ℝ)) ∞
      (fun z : Metric.sphere (0 : E) 1 × V =>
        (h (sphereIsotopyRadialCutoff z.2.val * t) z.1, z.2)) := by
  let V : TopologicalSpace.Opens ℝ := ⟨Set.Ioi 0, isOpen_Ioi⟩
  have hr : ContMDiff ((𝓡 d).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : Metric.sphere (0 : E) 1 × V => z.2.val) :=
    contMDiff_subtype_val.comp contMDiff_snd
  have hs : ContMDiff ((𝓡 d).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : Metric.sphere (0 : E) 1 × V => sphereIsotopyRadialCutoff z.2.val * t) :=
    (sphereIsotopyRadialCutoff_contDiff.mul (contDiff_const (c := t))).comp_contMDiff hr
  exact (hh.comp (hs.prodMk contMDiff_fst)).prodMk contMDiff_snd

run_cmd do
  let target := ``Submission.Diffeomorph.contMDiff_sphereIsotopyAnnulus_fixed_time
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Diffeomorph.contMDiff_sphereIsotopyAnnulus_fixed_time target :: scope.openDecls } }

open _root_.Diffeomorph in
private noncomputable def sphereIsotopyAnnulus
    (h : ℝ → Diffeomorph (𝓡 d) (𝓡 d) (Metric.sphere (0 : E) 1)
      (Metric.sphere (0 : E) 1) ∞)
    (hh : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 d)) (𝓡 d) ∞
      (fun z : ℝ × Metric.sphere (0 : E) 1 => h z.1 z.2))
    (hi : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 d)) (𝓡 d) ∞
      (fun z : ℝ × Metric.sphere (0 : E) 1 => (h z.1).symm z.2)) (t : ℝ) :
    let V : TopologicalSpace.Opens ℝ := ⟨Set.Ioi 0, isOpen_Ioi⟩
    Diffeomorph ((𝓡 d).prod 𝓘(ℝ, ℝ)) ((𝓡 d).prod 𝓘(ℝ, ℝ))
      (Metric.sphere (0 : E) 1 × V) (Metric.sphere (0 : E) 1 × V) ∞ := by
  let V : TopologicalSpace.Opens ℝ := ⟨Set.Ioi 0, isOpen_Ioi⟩
  let e : (Metric.sphere (0 : E) 1 × V) ≃ (Metric.sphere (0 : E) 1 × V) :=
    Equiv.prodCongrLeft (fun r : V => (h (sphereIsotopyRadialCutoff r.val * t)).toEquiv)
  exact
    { toEquiv := e
      contMDiff_toFun := contMDiff_sphereIsotopyAnnulus_fixed_time h hh t
      contMDiff_invFun :=
        contMDiff_sphereIsotopyAnnulus_fixed_time (fun s => (h s).symm) hi t }

run_cmd do
  let target := ``Submission.Diffeomorph.sphereIsotopyAnnulus
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Diffeomorph.sphereIsotopyAnnulus target :: scope.openDecls } }

open _root_.Diffeomorph in
private noncomputable def puncturedSphereIsotopy
    (h : ℝ → Diffeomorph (𝓡 d) (𝓡 d) (Metric.sphere (0 : E) 1)
      (Metric.sphere (0 : E) 1) ∞)
    (hh : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 d)) (𝓡 d) ∞
      (fun z : ℝ × Metric.sphere (0 : E) 1 => h z.1 z.2))
    (hi : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 d)) (𝓡 d) ∞
      (fun z : ℝ × Metric.sphere (0 : E) 1 => (h z.1).symm z.2)) (t : ℝ) :
    let U : TopologicalSpace.Opens E := ⟨{0}ᶜ, isOpen_compl_singleton⟩
    Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) U U ∞ :=
  ((unitSphereProd (E := E) (d := d) ∞).trans (sphereIsotopyAnnulus h hh hi t)).trans
    (unitSphereProd (E := E) (d := d) ∞).symm

run_cmd do
  let target := ``Submission.Diffeomorph.puncturedSphereIsotopy
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Diffeomorph.puncturedSphereIsotopy target :: scope.openDecls } }

open _root_.Diffeomorph in
private theorem contMDiff_puncturedSphereIsotopy
    (h : ℝ → Diffeomorph (𝓡 d) (𝓡 d) (Metric.sphere (0 : E) 1)
      (Metric.sphere (0 : E) 1) ∞)
    (hh : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 d)) (𝓡 d) ∞
      (fun z : ℝ × Metric.sphere (0 : E) 1 => h z.1 z.2))
    (hi : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 d)) (𝓡 d) ∞
      (fun z : ℝ × Metric.sphere (0 : E) 1 => (h z.1).symm z.2)) :
    let U : TopologicalSpace.Opens E := ⟨{0}ᶜ, isOpen_compl_singleton⟩
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun z : ℝ × U => puncturedSphereIsotopy h hh hi z.1 z.2) :=
  contMDiff_conjugated_diffeomorph_family
    (I := 𝓘(ℝ, E)) (J := (𝓡 d).prod 𝓘(ℝ, ℝ)) (K := 𝓘(ℝ, ℝ))
    (unitSphereProd (E := E) (d := d) ∞) (sphereIsotopyAnnulus h hh hi)
    (contMDiff_sphereIsotopyAnnulus h hh)

run_cmd do
  let target := ``Submission.Diffeomorph.contMDiff_puncturedSphereIsotopy
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Diffeomorph.contMDiff_puncturedSphereIsotopy target :: scope.openDecls } }

open _root_.Diffeomorph in
private theorem contMDiff_puncturedSphereIsotopy_symm
    (h : ℝ → Diffeomorph (𝓡 d) (𝓡 d) (Metric.sphere (0 : E) 1)
      (Metric.sphere (0 : E) 1) ∞)
    (hh : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 d)) (𝓡 d) ∞
      (fun z : ℝ × Metric.sphere (0 : E) 1 => h z.1 z.2))
    (hi : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 d)) (𝓡 d) ∞
      (fun z : ℝ × Metric.sphere (0 : E) 1 => (h z.1).symm z.2)) :
    let U : TopologicalSpace.Opens E := ⟨{0}ᶜ, isOpen_compl_singleton⟩
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun z : ℝ × U => (puncturedSphereIsotopy h hh hi z.1).symm z.2) :=
  contMDiff_conjugated_diffeomorph_family_symm
    (I := 𝓘(ℝ, E)) (J := (𝓡 d).prod 𝓘(ℝ, ℝ)) (K := 𝓘(ℝ, ℝ))
    (unitSphereProd (E := E) (d := d) ∞) (sphereIsotopyAnnulus h hh hi)
    (contMDiff_sphereIsotopyAnnulus (fun t => (h t).symm) hi)

run_cmd do
  let target := ``Submission.Diffeomorph.contMDiff_puncturedSphereIsotopy_symm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Diffeomorph.contMDiff_puncturedSphereIsotopy_symm target :: scope.openDecls } }

end Diffeomorph

end

section

open scoped _root_.ContDiff _root_.Manifold _root_.Topology

namespace Diffeomorph
open _root_.Diffeomorph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {d : ℕ} [Fact (Module.finrank ℝ E = d + 1)]
  (h : ℝ → Diffeomorph (𝓡 d) (𝓡 d) (Metric.sphere (0 : E) 1)
    (Metric.sphere (0 : E) 1) ∞)
  (hh : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 d)) (𝓡 d) ∞
    (fun z : ℝ × Metric.sphere (0 : E) 1 => h z.1 z.2))
  (hi : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 d)) (𝓡 d) ∞
    (fun z : ℝ × Metric.sphere (0 : E) 1 => (h z.1).symm z.2))

open _root_.Diffeomorph in
private theorem puncturedSphereIsotopy_apply_val (t : ℝ) :
    let U : TopologicalSpace.Opens E := ⟨{0}ᶜ, isOpen_compl_singleton⟩
    ∀ x : U, (puncturedSphereIsotopy h hh hi t x : E) =
      ((unitSphereProd (d := d) ∞ x).2 : ℝ) •
        (h (sphereIsotopyRadialCutoff ((unitSphereProd (d := d) ∞ x).2 : ℝ) * t)
          (unitSphereProd (d := d) ∞ x).1 : E) := by
  intro U x
  rfl

run_cmd do
  let target := ``Submission.Diffeomorph.puncturedSphereIsotopy_apply_val
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Diffeomorph.puncturedSphereIsotopy_apply_val target :: scope.openDecls } }

open _root_.Diffeomorph in
private theorem puncturedSphereIsotopy_symm_apply_val (t : ℝ) :
    let U : TopologicalSpace.Opens E := ⟨{0}ᶜ, isOpen_compl_singleton⟩
    ∀ x : U, ((puncturedSphereIsotopy h hh hi t).symm x : E) =
      ((unitSphereProd (d := d) ∞ x).2 : ℝ) •
        ((h (sphereIsotopyRadialCutoff ((unitSphereProd (d := d) ∞ x).2 : ℝ) * t)).symm
          (unitSphereProd (d := d) ∞ x).1 : E) := by
  intro U x
  rfl

run_cmd do
  let target := ``Submission.Diffeomorph.puncturedSphereIsotopy_symm_apply_val
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Diffeomorph.puncturedSphereIsotopy_symm_apply_val target :: scope.openDecls } }

open _root_.Diffeomorph in
private theorem norm_puncturedSphereIsotopy (t : ℝ) :
    let U : TopologicalSpace.Opens E := ⟨{0}ᶜ, isOpen_compl_singleton⟩
    ∀ x : U, ‖(puncturedSphereIsotopy h hh hi t x : E)‖ = ‖(x : E)‖ := by
  intro U x
  rw [puncturedSphereIsotopy_apply_val, norm_smul, Real.norm_eq_abs,
    abs_of_pos (unitSphereProd (d := d) ∞ x).2.property,
    mem_sphere_zero_iff_norm.mp (h _ _).property, mul_one,
    unitSphereProd_apply_snd_val]

run_cmd do
  let target := ``Submission.Diffeomorph.norm_puncturedSphereIsotopy
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Diffeomorph.norm_puncturedSphereIsotopy target :: scope.openDecls } }

open _root_.Diffeomorph in
private theorem puncturedSphereIsotopy_apply_of_fixed
    (hzero : h 0 = Diffeomorph.refl (𝓡 d) (Metric.sphere (0 : E) 1) ∞) (t : ℝ) :
    let U : TopologicalSpace.Opens E := ⟨{0}ᶜ, isOpen_compl_singleton⟩
    ∀ x : U, ‖(x : E)‖ ≤ 1 / 4 ∨ 2 ≤ ‖(x : E)‖ →
      puncturedSphereIsotopy h hh hi t x = x := by
  intro U x hx
  apply Subtype.ext
  rw [puncturedSphereIsotopy_apply_val, unitSphereProd_apply_snd_val,
    sphereIsotopyRadialCutoff_zero hx, _root_.MulZeroClass.zero_mul, hzero]
  change ‖(x : E)‖ • ((unitSphereProd (d := d) ∞ x).1 : E) = (x : E)
  rw [unitSphereProd_apply_fst_val,
    smul_inv_smul₀ (norm_ne_zero_iff.mpr (show (x : E) ≠ 0 from x.property))]

run_cmd do
  let target := ``Submission.Diffeomorph.puncturedSphereIsotopy_apply_of_fixed
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Diffeomorph.puncturedSphereIsotopy_apply_of_fixed target :: scope.openDecls } }

open _root_.Diffeomorph in
private theorem puncturedSphereIsotopy_zero
    (hzero : h 0 = Diffeomorph.refl (𝓡 d) (Metric.sphere (0 : E) 1) ∞) :
    let U : TopologicalSpace.Opens E := ⟨{0}ᶜ, isOpen_compl_singleton⟩
    puncturedSphereIsotopy h hh hi 0 = Diffeomorph.refl 𝓘(ℝ, E) U ∞ := by
  intro U
  apply Diffeomorph.ext
  intro x
  apply Subtype.ext
  rw [puncturedSphereIsotopy_apply_val, _root_.MulZeroClass.mul_zero, hzero]
  change ((unitSphereProd (d := d) ∞ x).2 : ℝ) •
    ((unitSphereProd (d := d) ∞ x).1 : E) = (x : E)
  rw [unitSphereProd_apply_snd_val, unitSphereProd_apply_fst_val,
    smul_inv_smul₀ (norm_ne_zero_iff.mpr (show (x : E) ≠ 0 from x.property))]

run_cmd do
  let target := ``Submission.Diffeomorph.puncturedSphereIsotopy_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Diffeomorph.puncturedSphereIsotopy_zero target :: scope.openDecls } }

open _root_.Diffeomorph in
private theorem puncturedSphereIsotopy_product_collar (t : ℝ)
    (θ : Metric.sphere (0 : E) 1) (r : ℝ) (hr : r ∈ Set.Icc (1 / 2 : ℝ) (3 / 2)) :
    let U : TopologicalSpace.Opens E := ⟨{0}ᶜ, isOpen_compl_singleton⟩
    ∀ x : U, (x : E) = r • (θ : E) →
      (puncturedSphereIsotopy h hh hi t x : E) = r • (h t θ : E) ∧
      ((puncturedSphereIsotopy h hh hi t).symm x : E) = r • ((h t).symm θ : E) := by
  intro U x hx
  have hrpos : 0 < r := by linarith [hr.1]
  have hxnorm : ‖(x : E)‖ = r := by
    rw [hx, norm_smul, Real.norm_eq_abs, abs_of_pos hrpos,
      mem_sphere_zero_iff_norm.mp θ.property, mul_one]
  have hdir : (unitSphereProd (d := d) ∞ x).1 = θ := by
    apply Subtype.ext
    rw [unitSphereProd_apply_fst_val, hxnorm, hx, inv_smul_smul₀ hrpos.ne']
  constructor
  · rw [puncturedSphereIsotopy_apply_val, unitSphereProd_apply_snd_val, hxnorm,
      hdir, sphereIsotopyRadialCutoff_one hr, one_mul]
  · rw [puncturedSphereIsotopy_symm_apply_val, unitSphereProd_apply_snd_val, hxnorm,
      hdir, sphereIsotopyRadialCutoff_one hr, one_mul]

run_cmd do
  let target := ``Submission.Diffeomorph.puncturedSphereIsotopy_product_collar
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Diffeomorph.puncturedSphereIsotopy_product_collar target :: scope.openDecls } }

end Diffeomorph

end

section

open scoped _root_.ContDiff _root_.Manifold _root_.Topology

namespace Diffeomorph
open _root_.Diffeomorph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {d : ℕ} [Fact (Module.finrank ℝ E = d + 1)]

open _root_.Diffeomorph in
theorem exists_isotopy_extension_sphere_product_collar
    (h : ℝ → Diffeomorph (𝓡 d) (𝓡 d) (Metric.sphere (0 : E) 1)
      (Metric.sphere (0 : E) 1) ∞)
    (hh : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 d)) (𝓡 d) ∞
      (fun z : ℝ × Metric.sphere (0 : E) 1 => h z.1 z.2))
    (hi : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 d)) (𝓡 d) ∞
      (fun z : ℝ × Metric.sphere (0 : E) 1 => (h z.1).symm z.2))
    (hzero : h 0 = Diffeomorph.refl (𝓡 d) (Metric.sphere (0 : E) 1) ∞) :
    ∃ H : ℝ → E ≃ₘ[ℝ] E,
      ContDiff ℝ ∞ (fun z : ℝ × E => H z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × E => (H z.1).symm z.2) ∧
      H 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞ ∧
      (∀ t x, ‖H t x‖ = ‖x‖ ∧ ‖(H t).symm x‖ = ‖x‖) ∧
      (∀ t x, ‖x‖ ≤ 1 / 4 ∨ 2 ≤ ‖x‖ → H t x = x ∧ (H t).symm x = x) ∧
      (∀ t (θ : Metric.sphere (0 : E) 1) r, r ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) →
        H t (r • (θ : E)) = r • (h t θ : E) ∧
        (H t).symm (r • (θ : E)) = r • ((h t).symm θ : E)) ∧
      ∀ t r, H t '' Metric.closedBall (0 : E) r = Metric.closedBall 0 r ∧
        H t '' Metric.ball (0 : E) r = Metric.ball 0 r ∧
        H t '' Metric.sphere (0 : E) r = Metric.sphere 0 r := by
  let U : TopologicalSpace.Opens E := ⟨{0}ᶜ, isOpen_compl_singleton⟩
  let e := puncturedSphereIsotopy h hh hi
  let C : Set E := {x | 1 / 4 ≤ ‖x‖ ∧ ‖x‖ ≤ 2}
  have hC : IsClosed C :=
    (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  have hCU : C ⊆ U := by
    intro x hx
    change x ≠ 0
    intro hx0
    have hxlow : (1 / 4 : ℝ) ≤ ‖x‖ := hx.1
    rw [hx0, norm_zero] at hxlow
    norm_num at hxlow
  have hfix : ∀ t (x : U), (x : E) ∉ C → e t x = x := by
    intro t x hx
    apply puncturedSphereIsotopy_apply_of_fixed h hh hi hzero t x
    change ¬ (1 / 4 ≤ ‖(x : E)‖ ∧ ‖(x : E)‖ ≤ 2) at hx
    rcases not_and_or.mp hx with hx | hx
    · exact Or.inl (le_of_lt (lt_of_not_ge hx))
    · exact Or.inr (le_of_lt (lt_of_not_ge hx))
  let H : ℝ → E ≃ₘ[ℝ] E := fun t => extend (e t) hC hCU (hfix t)
  have hpair : ContMDiff 𝓘(ℝ, ℝ × E) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun z : ℝ × E => (z.1, z.2)) :=
    contDiff_fst.contMDiff.prodMk contDiff_snd.contMDiff
  have hH : ContDiff ℝ ∞ (fun z : ℝ × E => H z.1 z.2) :=
    ((contMDiff_extend e (contMDiff_puncturedSphereIsotopy h hh hi) hC hCU hfix).comp
      hpair).contDiff
  have hHi : ContDiff ℝ ∞ (fun z : ℝ × E => (H z.1).symm z.2) :=
    ((contMDiff_extend_symm e (contMDiff_puncturedSphereIsotopy_symm h hh hi) hC hCU
      hfix).comp hpair).contDiff
  have hNorm : ∀ t x, ‖H t x‖ = ‖x‖ := by
    intro t x
    by_cases hx : x ∈ U
    · rw [show H t x = (e t ⟨x, hx⟩ : E) from extend_apply _ _ _ _ ⟨x, hx⟩]
      exact norm_puncturedSphereIsotopy h hh hi t ⟨x, hx⟩
    · rw [show H t x = x from extend_apply_of_notMem _ _ _ _ (fun h => hx (hCU h))]
  have hNormi : ∀ t x, ‖(H t).symm x‖ = ‖x‖ := by
    intro t x
    exact (hNorm t ((H t).symm x)).symm.trans (congrArg _root_.Norm.norm ((H t).apply_symm_apply x))
  refine ⟨H, hH, hHi, ?_, fun t x => ⟨hNorm t x, hNormi t x⟩, ?_, ?_, ?_⟩
  · apply Diffeomorph.ext
    intro x
    change H 0 x = x
    by_cases hx : x ∈ U
    · rw [show H 0 x = (e 0 ⟨x, hx⟩ : E) from extend_apply _ _ _ _ ⟨x, hx⟩]
      exact congrArg (fun f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) U U ∞ =>
        (f ⟨x, hx⟩ : E)) (puncturedSphereIsotopy_zero h hh hi hzero)
    · exact extend_apply_of_notMem _ _ _ _ (fun h => hx (hCU h))
  · intro t x hx
    have hfixed : H t x = x := by
      by_cases hxU : x ∈ U
      · rw [show H t x = (e t ⟨x, hxU⟩ : E) from extend_apply _ _ _ _ ⟨x, hxU⟩]
        exact congrArg Subtype.val
          (puncturedSphereIsotopy_apply_of_fixed h hh hi hzero t ⟨x, hxU⟩ hx)
      · exact extend_apply_of_notMem _ _ _ _ (fun h => hxU (hCU h))
    exact ⟨hfixed, (congrArg (H t).symm hfixed).symm.trans ((H t).symm_apply_apply x)⟩
  · intro t θ r hr
    have hrpos : 0 < r := by linarith [hr.1]
    have hxU : r • (θ : E) ∈ U := by
      change r • (θ : E) ≠ 0
      rw [← norm_ne_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hrpos,
        mem_sphere_zero_iff_norm.mp θ.property, mul_one]
      exact hrpos.ne'
    let x : U := ⟨r • (θ : E), hxU⟩
    rw [show H t (r • (θ : E)) = (e t x : E) from extend_apply _ _ _ _ x,
      show (H t).symm (r • (θ : E)) = ((e t).symm x : E) from
        extend_symm_apply _ _ _ _ x]
    exact puncturedSphereIsotopy_product_collar h hh hi t θ r hr x rfl
  · intro t r
    have himage (S : Set E) (hS : ∀ x, (H t).symm x ∈ S ↔ x ∈ S) : H t '' S = S :=
      ((H t).toEquiv.image_eq_preimage_symm S).trans (Set.ext hS)
    refine ⟨himage _ (fun x => ?_), himage _ (fun x => ?_), himage _ (fun x => ?_)⟩
    · simp only [Metric.mem_closedBall, dist_zero_right, hNormi]
    · simp only [Metric.mem_ball, dist_zero_right, hNormi]
    · simp only [Metric.mem_sphere, dist_zero_right, hNormi]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.exists_isotopy_extension_sphere_product_collar then
    throwError "Refusing to shadow existing declaration Diffeomorph.exists_isotopy_extension_sphere_product_collar"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.exists_isotopy_extension_sphere_product_collar ``Submission.Diffeomorph.exists_isotopy_extension_sphere_product_collar

end Diffeomorph

end
