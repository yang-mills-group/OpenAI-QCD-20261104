import YM.QCD.RP.Arc
import YM.Cells.Polar

/-!
# Local support and Cauchy Schwarz for reflected insertions
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.RP
open Lattice Wilson Grass Lat NormedSpace Function
open scoped BigOperators Matrix.Norms.Frobenius Matrix Topology ComplexOrder
variable {n : Side} {F : ℕ} {C : Lat.Cut n F} {R : Cells.Cut n} {S P : Set (Site n)}

-- normalize instances explicitly
instance (priority := low) (S : Set (Site n)) : Fintype S := Fintype.ofFinite _
abbrev Deck (S : Set (Site n)) (F : ℕ) := (S × Fiber) × Flavor F

def setDay (S : Set (Site n)) (d : Deck S F) : Modes n F := ((d.1.1.val,d.1.2),d.2)

def Floors (S : Set (Site n)) (x : Insertion n F) : Prop :=
  ∃ f : Grid n → Dirac (Deck S F), Continuous f ∧ LocalOn S f ∧ ∀ U,x U=pass (setDay S) (f U)

lemma sided (x : Insertion n F) : Floors R.sector x ↔ Sided R x := Iff.rfl
lemma lower_maps {x : Insertion n F} (h : Floors S x) (hu : S ⊆ P) : Floors P x := by
  obtain ⟨s,hs,h,H⟩ := h
  let i : Deck S F → Deck P F := fun x => ((⟨x.1.1.val,hu x.1.1.property⟩,x.1.2),x.2)
  refine ⟨fun U => pass i (s U), (pass i).toLinearMap.continuous_of_finiteDimensional.comp hs,
    fun U V e => congrArg (pass i) (h U V (agrees_mono e hu)), fun U => ?_⟩
  rw [H,← AlgHom.comp_apply,pass_comp]; rfl

lemma flooring_one : Floors S (1:Insertion n F) := ⟨fun _ => 1,continuous_const,(fun _ _ _ => rfl),fun U => by simp⟩
lemma flooring_add {x y : Insertion n F} (h : Floors S x) (e : Floors S y) : Floors S (x+y) := by
  obtain ⟨f,hf,hp,H⟩ := h; obtain ⟨g,hg,hq,K⟩ := e
  exact ⟨f+g,hf.add hg, fun U V u => congrArg₂ (·+·) (hp U V u) (hq U V u), fun i => by simp [H,K]⟩
lemma flooring_smul (c : ℂ) {x : Insertion n F} (h : Floors S x) : Floors S (c • x) := by
  obtain ⟨f,hf,hp,H⟩ := h; exact ⟨fun U => c • f U,by fun_prop, fun U V u => congrArg (c • ·) (hp U V u), fun i => by simp [H]⟩
lemma flooring_mul {x y : Insertion n F} (h : Floors S x) (e : Floors S y) : Floors S (x*y) := by
  obtain ⟨f,hf,hp,H⟩ := h; obtain ⟨g,hg,hq,K⟩ := e
  exact ⟨f*g,hf.mul hg, fun U V u => congrArg₂ (·*·) (hp U V u) (hq U V u), fun i => by simp [H,K]⟩
lemma invariant_add (x y : Insertion n F) (h : Invariant x) (e : Invariant y) : Invariant (x+y) := by
  intro k; rw [show transform k (x+y)=transform k x + transform k y from by ext1 i; exact map_add (slots F k) _ _,h,e]
lemma invariant_smul (x : Insertion n F) (h : Invariant x) (c : ℂ) : Invariant (c • x) := by
  intro k; rw [show transform k (c • x)=c • transform k x from by ext1 i; exact map_smul (slots F k) c _,h]

-- sign adjustment remains in set
lemma rolling_maps (k : Tape n) {x : Insertion n F} (h : Floors S x) : Floors S (k.roll x) := by
  obtain ⟨f,hf,he,H⟩ := h
  let M : Matrix (Deck S F) (Deck S F) ℂ := Matrix.diagonal fun i => k.stamp (i.1.1.val)
  let g := adapter M M
  have hu : (pass (setDay S)).comp g=(k.tape F).comp (pass (setDay S)) := by
    apply ext_atoms; rintro (i|i)
    · change pass _ (adapter M M (psi i))=k.tape F (pass _ (psi i))
      rw [adapt_psi]; simp [M,Matrix.diagonal_apply,ite_smul,setDay]
    change pass _ (adapter M M (bar i))=k.tape F (pass _ (bar i)); rw [adapt_bar]
    simp [M,Matrix.diagonal_apply,ite_smul,setDay]
  refine ⟨fun U => g (f U),g.toLinearMap.continuous_of_finiteDimensional.comp hf,
    fun U V u => congrArg g (he U V u), fun U => ?_⟩
  rw [Tape.rolls,H]; exact (AlgHom.congr_fun hu (f U)).symm

lemma affine_edge (s : Signed) (t x : Site n) (a) : affine s t (x+step a)=affine s t x+((posDir a).rotate s).vec := by rw [Step.vec_rotate]; simp [affine]; abel
lemma sees (s : Signed) (t : Site n) (U V : Grid n) (h : Set.MapsTo (affine s t) S P)
    (e : Agrees P U V) : Agrees S (pull s t U) (pull s t V) := by
  intro d H K
  have h₁ := h H
  have h₂ := h K
  rw [affine_edge] at h₂
  let i := (posDir d.2).rotate s
  change i.read U _ = i.read V _
  change affine s t d.1 + i.vec ∈ _ at h₂
  have hh : U (i.used (affine s t d.1))=V (i.used (affine s t d.1)) := by
    unfold Step.used; split
    next ht => exact e _ (by simpa [sub_eq_add_neg,Step.vec,ht] using h₂) (by simpa using h₁)
    next ht => exact e _ h₁ (by simpa [Step.vec,ht] using h₂)
  unfold Step.read; rw [hh]

lemma reflects_map {x : Insertion n F} (h : Floors S x) (hp : Set.MapsTo R.reflect S P) : Floors P (reflect R x) := by
  obtain ⟨q,w,e,r⟩ := h
  let i : Deck S F → Deck P F := fun x => ((⟨R.reflect x.1.1,hp x.1.1.property⟩,x.1.2),x.2)
  let Y := tilt (copies F (rides (Equiv.refl S) fun _ => lamp R.pos))
  let g := (pass i).toLinearMap.comp Y
  have hg' (x : Dirac (Deck S F)) : g x=pass i (Y x) := rfl
  have hg : (theta R).comp (pass (setDay S (F:=F))).toLinearMap=(pass (setDay P)).toLinearMap.comp g := by
    refine ext_reversing (fun x y => ?_) (fun x y => ?_) ?_ ?_
    · simp only [LinearMap.comp_apply,AlgHom.toLinearMap_apply,map_mul,theta_mul]
    · simp only [LinearMap.comp_apply,AlgHom.toLinearMap_apply,hg',Y,tilt_mul,map_mul]
    · simp only [LinearMap.comp_apply,AlgHom.toLinearMap_apply,hg',Y,map_one,theta,tilt_one]
    rintro (⟨⟨u,y⟩,f⟩|⟨⟨u,y⟩,f⟩)
    · change theta R (pass _ (psi (place u (y,f))))=pass _ (pass _ (Y (psi (place u (y,f)))))
      rw [pass_psi, show setDay S (place u (y,f))=place u.val (y,f) from rfl,theta_psi,show Y (psi (place u (y,f)))=_ from
        tilting_psi (Equiv.refl S) rfl ..]; simp only [map_sum,map_smul,pass_psi,pass_bar]; rfl
    change theta R (pass _ (bar (place u (y,f))))=pass _ (pass _ (Y (bar (place u (y,f)))))
    rw [pass_bar, show setDay S (place u (y,f))=place u.val (y,f) from rfl,theta_bar,show Y (bar (place u (y,f)))=_ from
      tilting_bar (Equiv.refl S) ..]; simp only [map_sum,map_smul,pass_bar,pass_psi]; rfl
  have hi₁ : Continuous ((pass i).toLinearMap) := (pass i).toLinearMap.continuous_of_finiteDimensional
  have ht : Continuous Y := tilt_cont _
  have hv : Continuous g := hi₁.comp ht
  have hq : Continuous (R.pullC su) := Wilson.continuous_pull _ _
  refine ⟨fun U => g (q (R.pullC su U)), hv.comp (w.comp hq), fun U V H => congrArg g (e _ _ (sees _ _ U V hp H)),fun U => ?_⟩
  rw [reflects,r]; exact LinearMap.congr_fun hg _

lemma pictures {x : Insertion n F} (h : Floors S x) (hp : Set.MapsTo R.reflect S P) : Floors P (picture R C x) := rolling_maps _ (reflects_map (rolling_maps _ h) hp)
lemma picture_inv {x : Insertion n F} (h : Invariant x) : Invariant (picture R C x) := Tape.roll_invariant _ _ (reflect_invariant _ _ (Tape.roll_invariant _ _ h))
lemma pictured (x : Insertion n F) : picture R C (picture R C x)=x := by simp only [picture,Tape.unroll,reflects_inv]
lemma pic_one : picture R C (1:Insertion n F)=1 := by
  have he : reflect R (1:Insertion n F)=1 := by ext1 U; simp [theta]
  simp [picture,Tape.roll_one,he]
lemma pic_mul (x y : Insertion n F) : picture R C (x*y)=picture R C y*picture R C x := by simp only [picture,Tape.roll_mul, reflects_mul]
lemma pic_add (x y : Insertion n F) : picture R C (x+y)=picture R C x+picture R C y := by ext1 U; simp [picture]
lemma pic_smul (x : Insertion n F) (c : ℂ) : picture R C (c • x)=(star c) • picture R C x := by ext1 U; simp [picture]

/-- RP for every actual link plane. -/
theorem link_positive (h : R.kind=.link) (hL : 2≤R.half.val) (hb : 0≤C.β) (hz : 0<C.partitionR)
    (x : Insertion n F) (H : Floors R.sector x) (hi : Invariant x) : 0 ≤ C.average (picture R C x*x) := by
  rw [← Tape.roll_average (mount R C) C (show (mount R C).start = _ from rfl),Tape.roll_mul,picture,Tape.unroll]
  exact reflected_positive h (tuned R C) hL hb (by rw [Tape.roll_normer _ _ rfl]; exact hz) _ ((sided _).mp (rolling_maps _ H)) ((mount R C).roll_invariant x hi)

private lemma conjugates (a b z w : ℂ) (A : 0 ≤ a) (B : 0 ≤ b)
    (H : ∀ c : ℂ, 0 ≤ a+c*z+star c*w+c*star c*b) : star z=w := by
  have ha := Complex.nonneg_iff.mp A; have hb := Complex.nonneg_iff.mp B
  have hr := Complex.nonneg_iff.mp (H 1)
  have hi := Complex.nonneg_iff.mp (H Complex.I)
  rw [Complex.nonneg_iff] at A B
  simp [Complex.mul_im, ← A.2, ← B.2] at hr hi
  apply Complex.ext <;> simp
  all_goals linarith

lemma sch (h : R.kind=.link) (hL : 2≤R.half.val) (hb : 0≤C.β) (hz : 0<C.partitionR)
    (x y : Insertion n F) (X : Floors R.sector x) (Y : Floors R.sector y) (H : Invariant x) (K : Invariant y) :
    ‖C.average (picture R C x*y)‖^2 ≤ ‖C.average (picture R C x*x)‖ * ‖C.average (picture R C y*y)‖ := by
  let L (x y : Insertion n F) := C.average (picture R C x*y)
  have ha : 0 ≤ L x x := link_positive h hL hb hz _ X H
  have hb' : 0 ≤ L y y := link_positive h hL hb hz _ Y K
  have he (c : ℂ) : 0 ≤ L x x+c*L x y + star c*L y x + c*star c*L y y := by
    have hi : 0 ≤ L (x+c • y) (x+c • y) := link_positive h hL hb hz _
      (flooring_add X (flooring_smul _ Y)) (invariant_add _ _ H (invariant_smul _ K _))
    apply hi.trans_eq
    unfold L; rw [pic_add,pic_smul]; simp only [add_mul,mul_add,mul_smul_comm,smul_mul_assoc,map_add,map_smul, smul_eq_mul]; ring
  apply Cells.schwarz ha hb'; intro t
  have hr := he (star t); rw [star_star] at hr
  have hk := conjugates (L x x) (L y y) (L x y) (L y x) ha hb' he
  rw [mul_comm (star t) t,← hk] at hr
  exact hr -- check terms
end YM.QCD.RP
