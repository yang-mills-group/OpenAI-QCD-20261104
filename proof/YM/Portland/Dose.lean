import YM.Massive.PCAC.Smalt
/-! Four Leg calculations. s then t then u then v. h body character. Avoid jets.Index. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Grass.Ovule
open Function Finset NormedSpace
open scoped BigOperators Topology ContDiff Classical
variable {A:Type*}[Fintype A]
variable (i:A)(x y:Alg A)
noncomputable def core (A:Type*)[Fintype A]: Alg A→ₐ[ℂ] ℂ:={coef (∅:Finset A) with
 map_zero':=map_zero (coef (∅:Finset A))
 map_one':=by simpa using read (∅:Finset A)
 map_mul':=by
    intro x y; have hz(s t:Finset A):coef ∅ (mono s*mono t)=coef ∅ (mono s) * coef ∅ (mono t):=by
        by_cases h:s=∅; · subst s; simp [show coef (∅:Finset A) 1=1 by simpa using read (∅:Finset A)]
        by_cases hv:t=∅; · subst t; simp [show coef (∅:Finset A) 1=1 by simpa using read (∅:Finset A)]
        rw [read_other _ _ (Ne.symm h),zero_mul]; exact spectrum (layer_mul (homogeneous s) (homogeneous t)) _ (by simp only [card_empty]; have hx:s.card>0:=card_pos.mpr (nonempty_iff_ne_empty.mpr h); omega)
    change coef ∅ (x*y)=coef ∅ x*coef ∅ y; nth_rw 1 2 [←write x]; nth_rw 1 2 [←write y]; simp only [map_sum,map_smul, sum_mul,mul_sum,smul_eq_mul,smul_mul_assoc,mul_smul_comm,smul_sum]; refine sum_congr rfl fun s _=> sum_congr rfl fun t _=>?_ ; rw [hz]; ring
 commutes':=fun z=>by
     change coef ∅ _= _; rw [Algebra.algebraMap_eq_smul_one,map_smul,show coef (∅:Finset A) 1 =1 from ?_]; · exact mul_one z
     simpa using read (∅:Finset A)
}
local notation "μ"=> core _
lemma blind : μ (grade x)= μ x :=by
    nth_rw 1 2 [← write x]; simp_rw [map_sum,map_smul]; apply sum_congr rfl; intro s _; by_cases h:s=∅; · subst s; simp
    change coef s x • coef ∅ (grade (mono s))= coef s x • coef ∅ (mono s); rw [read_other _ _ (Ne.symm h)]; apply congr_arg (coef s x • ·)
    obtain ⟨w,-,-,he⟩:=expression s; rw [he]; apply spectrum (?_ : grade (List.ofFn _).prod ∈ layer A s.card) _ (by simpa only [card_empty,ne_eq,eq_comm,card_eq_zero] using h)
    have hv(l:List A): grade ((l.map atom).prod)∈ layer A l.length:=by induction l with|nil=> simpa using homogeneous (∅:Finset A)|cons a l ih=> simp only [List.map_cons,List.prod_cons,map_mul,grade_atom,List.length_cons,add_comm l.length]; exact layer_mul (Submodule.neg_mem _ (atom_mem _)) ih
    simpa only [List.length_ofFn,List.map_ofFn] using hv (List.ofFn w)
lemma minus_core (h:Minus x): μ x=0:=by have h':grade x= -x:=h; have hz:=blind x; rw [h',map_neg] at hz; exact neg_eq_self.mp hz -- name
lemma flipV : grade (vary i x)= -vary i (grade x):=by
    have hf(l:List A) : grade (vary i (l.map atom).prod)= - vary i (grade (l.map atom).prod):=by
        induction l with
        | nil=> simp [vary_one]
        | cons a l ih=> simp only [List.map_cons,List.prod_cons,map_mul,grade_atom,map_neg,neg_mul,vary_head,map_smul,map_sub,ih,mul_neg]; abel
    have ht(s:Finset A):grade (vary i (mono s))= -vary i (grade (mono s)):=by obtain ⟨w,-,-,h⟩:=expression s; rw[h]; simpa only [List.map_ofFn] using hf (List.ofFn w)
    nth_rw 1 2 [←write x]; simp only [map_sum,map_smul,ht,smul_neg,sum_neg_distrib]
/- direction map includes finitely many sites. -/
noncomputable def spr (d:A→ℂ): Alg A→ₗ[ℂ]Alg A:= ∑ i:A,d i • vary i
variable (d a b c:A→ℂ)
lemma turns : spr d x=∑ i:A,d i • vary i x:=by simp [spr]
lemma clap : spr d (x*y)= spr d x*y+grade x *spr d y:=by simp only [turns,vary_mul,mul_sum,sum_mul,smul_add,sum_add_distrib,smul_mul_assoc,mul_smul_comm]
lemma tall (h:Plus x):Minus (spr a x):=by change grade _= -_; simp_rw [turns,map_sum,map_smul,flipV,show grade x=x from h,smul_neg]; rw [sum_neg_distrib] -- h reducible typo
lemma dusk (h:Minus x):Plus (spr a x):=by change grade _=_; simp_rw [turns,map_sum,map_smul,flipV,show grade x= -x from h,map_neg,neg_neg]
lemma vanish (h:Plus x) : μ (spr a x)=0:= minus_core _ (tall x a h)
lemma wall (h:Plus x): spr a (exp x)=exp x*spr a x:=by rw[turns,turns,mul_sum]; simp only [varies_exp _ _ h,mul_smul_comm]
lemma cover (h:Plus x): Plus (exp x):=by change grade _=_; rw[map_weight (grade),show grade x=x from h] -- grade ring?
lemma spike (h:Plus x): μ (spr b (spr a (exp x)))= μ (exp x)*μ (spr b (spr a x)):=by
    rw [wall x a h,clap,map_add,map_mul,map_mul, vanish _ b (cover x h), show grade (exp x)=exp x from cover x h, zero_mul,zero_add]
set_option maxRecDepth 8000
set_option maxHeartbeats 400000
lemma quadruple (hx:Plus x)(hy:Plus y): μ (spr d (spr c (spr b (spr a (x*y)))))= μ (spr d (spr c (spr b (spr a x))))* μ y+ μ x * μ (spr d (spr c (spr b (spr a y))))+μ (spr b (spr a x))* μ (spr d (spr c y))- μ (spr c (spr a x))* μ (spr d (spr b y))+ μ (spr d (spr a x))* μ (spr c (spr b y))+ μ (spr c (spr b x))* μ (spr d (spr a y))- μ (spr d (spr b x))* μ (spr c (spr a y))+ μ (spr d (spr c x))* μ (spr b (spr a y)):=by
    have hZ(w): grade (spr w x)= -spr w x:=tall x w hx; have hp(w v):Plus (spr w (spr v x)):= dusk _ _ (tall x v hx); have hp'(w v):grade (spr w (spr v x))=spr w (spr v x):=hp w v; have hY(w v): Plus (spr w (spr v y)) := dusk _ _ (tall y v hy); have hf(w v z):grade (spr w (spr v (spr z x)))= -spr w (spr v (spr z x)):=tall _ _ (hp ..)
    simp only [clap,map_add,hZ,map_neg,show grade x=x from hx,map_mul,hp',vanish x _ hx,vanish y _ hy, vanish _ _ (hp ..), vanish _ _ (hY ..),hf]
    ring
lemma flow (h:Plus x): μ (spr d (spr c (spr b (spr a (exp x)))))= μ (exp x)*(μ (spr d (spr c (spr b (spr a x))))+ μ (spr d (spr c x))*μ (spr b (spr a x))-μ (spr d (spr b x))* μ (spr c (spr a x))+ μ (spr c (spr b x))* μ (spr d (spr a x))):=by
    let K:=exp x; have hK:Plus K:=cover x h
    have hZ(w):grade (spr w K)= -spr w K:=tall _ _ hK; have hp(w v): Plus (spr w (spr v K)):= dusk _ _ (tall _ _ hK); have hp'(w v): grade (spr w (spr v K))=spr w (spr v K):=hp w v
    rw [wall x a h]; change μ (spr d (spr c (spr b (K * spr a x))))= _
    simp only [clap,map_add,map_mul,hZ,map_neg,hp',show grade K=K from hK, vanish K _ hK,vanish x a h]; unfold K; simp_rw [spike x _ _ h]; ring
-- a=dbar b, b=dpsi a, c=dbar a, d=dpsi b. off Flavor.Slots undefined equality relation. E_ab=E_ac? c and a both bars must vanish. E_ad ψb*barb survives. Eb,c survives. 
lemma eon (hx:Plus x)(hy:Plus y)(h₁:μ (spr b (spr a x))=0)(h₂:μ (spr d (spr b x))=0)(h₃:μ (spr c (spr a x))=0)(h₄:μ (spr d (spr c x))=0):
    μ (spr d (spr c (spr b (spr a (exp x*y)))))= μ (exp x)*(μ (spr d (spr c (spr b (spr a y)))) + μ y*(μ (spr d (spr c (spr b (spr a x))))+ μ (spr c (spr b x))* μ (spr d (spr a x)))+ μ (spr d (spr a x))* μ (spr c (spr b y))+ μ (spr c (spr b x))* μ (spr d (spr a y))):=by
      rw [quadruple _ _ _ _ _ _ (cover x hx) hy,flow x d a b c hx]; simp only [spike x _ _ hx,h₁,h₂,h₃,h₄]; ring
end YM.QCD.Grass.Ovule
#print axioms YM.QCD.Grass.Ovule.eon
