import YM.QCD.Creek.Crest
/-!
# sanity: joint Gaussian adjoint ingredients (contact map)
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Tide
open Function NormedSpace Matrix Finset Grass Creek
open scoped BigOperators Matrix Topology
variable {A B C M: Type*}[Fintype A][Fintype B][Fintype C][Fintype M]
variable (F:Pairs A ↪ M) [DecidableEq A]
noncomputable abbrev whip := birth (pond F 1)
noncomputable abbrev winter (A:Type*)[Fintype A][DecidableEq A]: EndA (Pairs A):= whip (Embedding.refl _)
lemma advanceP (i:A)(x:Alg M) : whip F (atom (pet F i)*x)= atom (pet F i)*whip F x + whip F (vary (met F i) x):=by
     rw [show whip F (atom (pet F i)*x)= (whip F*l (pet F i)) x from rfl, show whip F*l (pet F i)= l (pet F i)*whip F+whip F*slotP F 1 i from earnsP ..]; suffices hu: slotP F 1 i=v (met F i) by rw [hu]; rfl
     rw [slotP,sum_eq_single i]
     · rw [Matrix.one_apply_eq,one_smul]
     · intro j _ h; rw [Matrix.one_apply_ne (Ne.symm h)]; exact zero_smul ℂ (v (met F j))
     simp
lemma advanceM (i:A)(x:Alg M): whip F (atom (met F i)*x)=atom (met F i)*whip F x- whip F (vary (pet F i) x):=by
     rw [show whip F (atom (met F i)*x)= (whip F*l (met F i)) x from rfl, show (whip F*l (met F i))= l (met F i)*whip F+whip F *slotM F 1 i from earnsM ..]
     suffices he: slotM F 1 i= -v (pet F i) by rw [he]; change atom _ * _ + whip F (-(vary _ x)) =_; rw [map_neg,sub_eq_add_neg]; rfl
     apply ContinuousLinearMap.ext; intro x; simp only [slotM,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply, Matrix.one_apply,neg_smul,ite_smul]; simp
lemma cheers: whip F 1=1:=powers _ _ (by simp [pond,v,vary_one])
structure Recursor {Y:Type*}[Fintype Y] (J:Dirac A→ₗ[ℂ] Alg Y) (f:Pairs A→ M) (cr: M → Alg Y) :Prop where
    goP(i:A)(x:Dirac A): J (psi i*x)= cr (f (.inl i))*J x + J (vary (Sum.inr i:Pairs A ) x)
    goM(i:A)(x:Dirac A): J (bar i*x)= cr (f (.inr i))*J x - J (vary (Sum.inl i: Pairs A) x)
omit [DecidableEq A] in
lemma story {Y:Type*}[Fintype Y] {f:Pairs A→M}{C: M→Alg Y}{U V:Dirac A→ₗ[ℂ]Alg Y}(h: Recursor U f C)(hw: Recursor V f C)(hu:U 1=V 1): U=V:=by
    classical
    have he(n:ℕ):∀ L:List (Pairs A), L.length≤n → U (L.map atom).prod= V (L.map atom).prod:=by
         induction n with
         | zero=> intro L h; simp only [Nat.le_zero,List.length_eq_zero_iff] at h; rw [h]; exact hu
         | succ n ih=>
           have hv (s:List (Pairs A))(hv:s.length≤n)(i:Pairs A): U (vary i (s.map atom).prod)=V (vary i (s.map atom).prod):=by
              let x:=vary i (s.map atom).prod; change U x=V x; rw [← write x,map_sum,map_sum]; refine sum_congr rfl fun j _=>?_
              by_cases hj: j.card=s.length-1
              · simp only [map_smul]; congr 1
                obtain ⟨w,-,-,hw⟩:=expression j; rw [hw]
                simpa only [List.map_ofFn] using ih (List.ofFn w) (by rw [List.length_ofFn,hj]; omega)
              rw [show coef j x=0 from spectrum (lower_layer i s) _ hj]; simp
           intro s hs; cases s with
           | nil=> exact ih [] (by simp)
           | cons i s=>
               have ht:=show s.length ≤ n by simpa using hs
               rcases i with i|i
               · change U (psi i*(s.map atom).prod)= V (psi i*(s.map atom).prod); rw [h.goP,hw.goP,ih _ ht,hv s ht]
               change U (bar i*(s.map atom).prod)= V (bar i*(s.map atom).prod); rw [h.goM,hw.goM,ih _ ht,hv s ht]
    apply LinearMap.ext; intro x; rw [← write x,map_sum,map_sum]; apply sum_congr rfl; intro i _; rw [map_smul,map_smul]; congr 1
    obtain ⟨w,-,-,hw⟩:= expression i; rw [hw]; simpa only [List.map_ofFn] using he _ (List.ofFn w) le_rfl
-- extend whip
lemma storms (x:Dirac A):whip F (embed F x)=embed F (winter _ x):=by
    let T:= (whip F).toLinearMap.comp (embed F).toLinearMap; let Y:= (embed F).toLinearMap.comp (winter _).toLinearMap; change T x=Y x; apply LinearMap.congr_fun _ x
    refine story (f:=⇑F) (C:=atom) ⟨fun i x=>?_,fun i x=>?_⟩ ⟨fun i x=>?_,fun i x=>?_⟩ ?_
    · change whip F (embed F (atom _ *x))=_; rw [map_mul,embed_atom]; change whip F (atom (pet F i)*embed F x)=_; rw [advanceP F i]; exact congrArg (fun a=> _ + whip F a) (survives F.injective (.inr i) x)
    · change whip F (embed F (atom _ *x))=_; rw [map_mul,embed_atom]; change whip F (atom (met F i)*embed F x)=_; rw [advanceM F i]; exact congrArg (fun a=> _ - whip F a) (survives F.injective (.inl i) x)
    · change embed F (winter _ (psi i*x))=_; rw [show winter A (psi i*x)=_ from advanceP (Embedding.refl (Pairs A)) i x,map_add,map_mul,embed_atom]; rfl
    · change embed F (winter _ (bar i*x))=_; rw [show winter A (bar i*x)=_ from advanceM (Embedding.refl (Pairs A)) i x,map_sub,map_mul,embed_atom]; rfl
    change whip F (embed F 1)=embed F (winter _ 1); simp [winter,cheers]
end YM.QCD.Tide
