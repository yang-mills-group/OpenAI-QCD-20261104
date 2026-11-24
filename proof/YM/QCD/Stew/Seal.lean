import YM.QCD.Stew.Pump
/-! # balanced degree pair. Derivative fees are paid from the single load. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stew
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N:ℕ} {t:ℝ} {o: Site c}
variable {D K:Type*} [Fintype D][DecidableEq D]

lemma vacant (X:Matrix D D ℂ)(x:Dirac D): coef ∅ (disguise X x)=coef ∅ x:=by rw [show coef ∅ (disguise X x)=coef ∅ (panel 0 (disguise X x)) from Eq.symm (by simp only [angel,card_empty,if_true])]; rw [sport,bush,map_smul, map_one, map_smul]; simp_rw [← mono_empty, Grass.read, smul_eq_mul,mul_one] -- angel rw fails
lemma vax (x:Dirac D):coef ∅ (surf _ x)=star (coef ∅ x):=by rw [show coef ∅ (surf _ x)=coef ∅ (panel 0 (surf _ x)) from Eq.symm (by simp only [angel,card_empty,if_true])]; rw [toned,bush,map_smulₛₗ,surf_one,map_smul]; simp_rw [← mono_empty, Grass.read,smul_eq_mul,mul_one]; rfl

def tag (i j:D): Finset (Pairs D):={.inl j,.inr i}
lemma tagged (a b c d:D): tag a b=tag c d ↔ a=c ∧ b=d:=by
   constructor; swap; · rintro ⟨rfl,rfl⟩; rfl
   intro he; have hx: Sum.inl b∈tag c d:= he ▸ (show _∈tag a b by simp [tag]); have hp: Sum.inr a ∈tag c d:=he ▸ (show _∈tag a b by simp [tag]); exact ⟨by simpa [tag] using hp,by simpa [tag] using hx⟩
lemma plum (i j:D): psi j*bar i=mono (tag i j) ∨ psi j*bar i=-mono (tag i j):=by -- replace
   have h:= mono_mul_sign ({Sum.inl j}:Finset (Pairs D)) {Sum.inr i} (by simp); rw [mono_single,mono_single] at h; rw [show (Finset.disjUnion _ _ _) =tag i j from ?_] at h; exact h
   ext; simp [tag]
def bit (i j:D):ℂ:= coef (tag i j) (psi j * bar i)
lemma bitS (i j:D):bit i j=1∨ bit i j=-1:=by unfold bit; rcases plum i j with h|h <;> simp [h]
lemma plumB (i j:D):psi j*bar i=bit i j • mono (tag i j):=by unfold bit; rcases plum i j with h|h <;> simp [h]
lemma biform (X:Matrix D D ℂ)(s: Finset (Pairs D)):coef s (form X)=∑ i,∑ j,(if s=tag i j then bit i j * X i j else 0):=by
   unfold form; simp_rw [map_sum, map_smul,plumB, map_smul]; refine sum_congr rfl fun i _=> sum_congr rfl (fun j _=>?_) ; split
   next h=> rw [h,Grass.read,smul_eq_mul,smul_eq_mul,mul_one,mul_comm]
   next h=> rw [read_other _ _ h,smul_zero,smul_zero]
def grasp (x:Dirac D): Matrix D D ℂ:= Matrix.of fun i j => bit i j*coef (tag i j) x
lemma gravid (D':Matrix D D ℂ): grasp (form D')=D':=by
   ext i j; change bit i j*coef _ _=_; rw [biform,_root_.Finset.sum_eq_single i]
   · rw [sum_eq_single j]; swap; · intro k _ hk; rw [if_neg (mt (tagged ..).1 (fun h=> hk h.2.symm))]
     rotate_left; · simp
     rw [if_pos rfl]
     rcases bitS i j with h|h <;> rw [h] <;> ring
   · intro b _ hb; apply sum_eq_zero; intro k hk; rw [if_neg (mt (tagged ..).1 (fun h=> hb h.1.symm))]
   simp
lemma grub (x y:Dirac D): grasp (x+y)=grasp x+grasp y:=by ext i j; simp [grasp,mul_add]
lemma regalia (x:Dirac D)(b:ℂ): grasp (b • x)=b • grasp x:=by ext; simp [grasp]; ring
lemma breast (x:Dirac D): grasp (panel 2 x)=grasp x:=by
   ext i j; change _*coef _ _ = _; rw [angel,if_pos (show (tag i j).card=2 by simp [tag])]; rfl
lemma graces (X Y:Matrix D D ℂ)(hh: form X=form Y):X=Y:=by rw [← gravid X,←gravid Y, hh]
lemma kent (x:Dirac D)(h:∀ s : Finset (Pairs D), s.card=2→ (∀ i j,s≠tag i j) → coef s x=0): panel 2 x=form (grasp x):=by
   apply poster; intro i; rw [angel]; split
   next hp=>
      by_cases he : ∃ a b,i=tag a b
      · obtain ⟨a,b,rfl⟩:=he; have ht:=gravid (grasp x); have h: bit a b≠0:=by rcases bitS a b with h|h <;> simp [h]
        exact mul_left_cancel₀ h (by exact congr_fun (congr_fun ht a) b|>.symm)
      rw [h _ hp (by simpa using he), biform]; push Not at he; simp [he]
   next h=> exact (spectrum (form_two _) _ h).symm

lemma angle (d:ℂ)(i:D): disguise (d • (1:Matrix D D ℂ)) (psi i)= d • psi i ∧ disguise (d • (1:Matrix D D ℂ)) (bar i)= star d • bar i:=by
   unfold disguise; rw [adapt_psi, adapt_bar]; simp only [Matrix.smul_apply, Matrix.one_apply, Matrix.transpose_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]; constructor <;> rw [sum_eq_single i]
   all_goals first | solve | intro j _ he; simp [he,he.symm]| simp
lemma unbalanced (x:Dirac D)(hv:disguise (Complex.I • 1) x=x)(i:Finset (Pairs D))(hi:i.card=2)(ht:∀ a b,i≠tag a b): coef i x=0:=by
   let T:=disguise (Complex.I • (1:Matrix D D ℂ))
   have hh (L: List (Pairs D)): ∃ k:ℂ,T (L.map atom).prod=k • (L.map atom).prod:=by
      induction L with
      | nil=> exact ⟨1,by simp⟩
      | cons i L ih =>
         obtain ⟨d,h⟩:=ih; cases i with
         | inl i=> refine ⟨Complex.I*d,?_⟩; rw [List.map_cons,List.prod_cons,map_mul,h, show T (atom (.inl i))=_ from (angle _ _).1]; rw [smul_mul_smul_comm]
         | inr i=> refine ⟨star Complex.I*d,?_⟩; rw [List.map_cons,List.prod_cons,map_mul,h, show T (atom (.inr i))=_ from (angle _ _).2]; rw [smul_mul_smul_comm]
   choose k hk using fun s: Finset (Pairs D)=> (show ∃ d:ℂ,T (mono s)=d • mono s from by obtain ⟨w,-,-,hw⟩:=expression s; rw [hw]; simpa only [List.map_ofFn] using hh (List.ofFn w))
   have hT:T (mono i) = -mono i :=by
     obtain ⟨a,b,h,rfl⟩:= card_eq_two.mp hi -- order
     have hj:T (atom a*atom b)=-(atom a*atom b):=by
       rw [map_mul]; rcases a with a|a<;> rcases b with b|b
       · rw [show T (atom (.inl a))=_ from (angle _ _).1,show T (atom (.inl b))=_ from (angle _ _).1,smul_mul_smul_comm,Complex.I_mul_I]; simp [psi]
       · exact False.elim (ht b a rfl)
       · exact False.elim (ht a b (by unfold tag; ext; simp; tauto))
       rw [show T (atom (.inr a))=_ from (angle _ _).2,show T (atom (.inr b))=_ from (angle _ _).2,smul_mul_smul_comm,← star_mul',Complex.I_mul_I]; simp [bar] -- star_mul' name
     have hf:= mono_mul_sign ({a}:Finset (Pairs D)) {b} (by simp [h]); simp_rw [disjUnion_eq_union,singleton_union,mono_single] at hf; rcases hf with hf|hf; · rwa [hf] at hj
     rw [hf,map_neg,neg_neg] at hj; exact ((neg_neg _).symm.trans (congr_arg Neg.neg hj))
   have he: coef i x= -(coef i x):=by
      have hh': T x=x:=hv
      nth_rw 1 [←hh',←write x]; simp_rw [map_sum,map_smul]; rw [sum_eq_single i]
      · rw [hT, map_neg, Grass.read]; simp
      · intro j _ hj; rw [hk,map_smul, read_other _ _ hj.symm]; simp
      simp
   apply Complex.ext; · have hp:=congr_arg Complex.re he; rw [Complex.neg_re] at hp; rw [Complex.zero_re]; linarith
   have hp:=congr_arg Complex.im he; rw [Complex.neg_im] at hp; rw [Complex.zero_im]; linarith
end YM.QCD.Stew
