import YM.QCD.Door.Ring
/-!
  # Positive aux inner prod on words. The operators preserve it if raw spin on generators unitary. Need not assume invariant metric in original norm. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.Sprig.Chloe
open Function Filter Matrix Set Module Finset QCD QCD.Lat QCD.Grass QCD.Creek
open scoped BigOperators Topology Classical Matrix Matrix.Norms.L2Operator InnerProductSpace ComplexOrder
variable {X:Type}[Fintype X] {Y:Type}[Fintype Y](p:X)
noncomputable def poly(x y:Alg X):ℂ:= ∑ i:Finset X, star (coef i x)*coef i y
lemma lumenL(a b c:Alg X) : poly (a+b) c=poly a c+poly b c:=by simp only[poly,map_add,star_add, add_mul, Finset.sum_add_distrib]
lemma lumen(a b c:Alg X): poly a (b+c)=poly a b+poly a c:=by simp only[poly,map_add,mul_add, Finset.sum_add_distrib]
lemma senseL(a b:Alg X)(t:ℂ): poly (t • a) b=star t*poly a b:=by unfold poly; rw [mul_sum]; apply Finset.sum_congr rfl; intro i _; rw[map_smul, smul_eq_mul,star_mul']; ring
lemma sense (a b:Alg X)(t:ℂ) : poly a (t • b)=t * poly a b:=by unfold poly; rw[mul_sum]; apply sum_congr rfl; intro i _; rw[map_smul,smul_eq_mul]; ring
lemma sun (x y:Alg X):star (poly x y)=poly y x:=by unfold poly; rw [star_sum]; apply Finset.sum_congr rfl; intro i _; rw[star_mul,star_star]
noncomputable def rightP (x:Alg X): Alg X→ₗ[ℂ]ℂ where
    toFun:= poly x
    map_add':=lumen x
    map_smul' t y:=sense x y t
noncomputable def leftP(x:Alg X): Alg X→ₛₗ[starRingEnd ℂ]ℂ where
    toFun y:=poly y x
    map_add' y z:=lumenL y z x
    map_smul' t y:=senseL y x t
lemma lunar {A:Type}(u:Finset A)(x:A→ Alg X)(y:Alg X): poly y (∑ i∈u,x i)= ∑ i∈u,poly y (x i) := map_sum (rightP y) _ _
lemma lunarL{A:Type}(u:Finset A)(x:A→Alg X)(y:Alg X): poly (∑ i∈u,x i) y=∑ i∈u,poly (x i) y:=map_sum (leftP y) _ _
lemma core (s:Finset X)(x:Alg X):poly (mono s) x=coef s x:=by unfold poly; rw [sum_eq_single s]; simp; intro i _ h; rw[Grass.read_other _ _ h,star_zero, zero_mul]; simp -- simp ordering
lemma polar(a b:Finset X):poly (mono a) (mono b)= if a=b then 1 else 0 :=by
     split
     next h=>subst a; rw [core]; simp
     next h=>rw [core]; exact Grass.read_other _ _ h
lemma posH (x:Alg X):0 ≤ poly x x := by unfold poly; exact sum_nonneg fun i _=>star_mul_self_nonneg _ -- check
lemma onlyH(x:Alg X)(h:x≠0):0 < poly x x:=by
    refine (posH x).lt_of_ne ?_; intro he; have hg:=he.symm; unfold poly at hg; have hh(i: Finset X):coef i x=0:=by have hv : star (coef i x)*coef i x=0:= Finset.sum_eq_zero_iff_of_nonneg (fun j _=>star_mul_self_nonneg _) |>.mp hg i (mem_univ _); simpa using hv -- prefix
    apply h; rw [← write x]; simp [hh]
-- creation and annihilation. mutual transposition irrespective of blade signs. prove via coefficients.
variable (i:X)(s t:Finset X)
lemma hush (h:i∉s):vary i (mono s)=0:=by
    obtain ⟨f,-,hp,hf⟩:=expression s
    have hh(l:List X)(hx:i∉l): vary i (l.map atom).prod=0:=by
           induction l with|nil=>simp [vary_one]|cons p l ih=>simp only [List.mem_cons,not_or] at hx; simp only[List.map_cons,List.prod_cons,vary_mul,vary_off _ _ hx.1, ih hx.2,mul_zero,zero_mul,add_zero]
    rw[hf]; have ht:i∉List.ofFn f:=by simpa [hp] using h
    simpa only [List.map_ofFn] using hh (List.ofFn f) ht
lemma ash (h:i∈s) : atom i *mono s=0:=by rw [←mono_single]; exact mono_mul_zero _ _ (by simpa using h)
-- sign relation from previous.
lemma glows (h:i∉s):∃ ε:ℂ, (ε=1 ∨ ε= -1) ∧ atom i*mono s= ε • mono (insert i s) ∧ vary i (mono (insert i s))= ε • mono s:=by
     have he :vary i (atom i*mono s)=mono s:=by rw [vary_mul,vary_self,one_mul,hush _ _ h,mul_zero,add_zero]; -- Simp `hush` arguments implicit
     have hx:=mono_mul_sign {i} s (by simpa using h); simp only[Finset.disjUnion_eq_union,Finset.singleton_union,mono_single] at hx
     rcases hx with hx|hx
     · exact ⟨1,Or.inl rfl,by rw [hx,one_smul],by rw[hx] at he; rw [one_smul,he]⟩
     rw[hx,map_neg] at he; refine ⟨-1,Or.inr rfl,by rw [hx,neg_one_smul],?_⟩; rw [neg_one_smul,← he,neg_neg] -- replacing mono s maybe also elsewhere
lemma creating :poly (atom i * mono s) (mono t)=poly (mono s) (vary i (mono t)):=by
     by_cases he:i∈t
     · let u:= t.erase i; have hx: i∉u:=Finset.notMem_erase i t; obtain ⟨a,hA,h1,h2⟩:=glows i u hx
       have hE:insert i u=t:= insert_erase he; rw [hE] at h1 h2
       by_cases hs:i∈s
       · rw [ash _ _ hs,h2]; have hp:s≠u:= fun h=>hx (h ▸ hs); rw[sense,polar,if_neg hp,mul_zero]; simp[poly]
       by_cases hu:s=u
       · rw [hu,h1,h2,sense,senseL]; simp_rw [polar]; simp [show star a=a from (by rcases hA with h|h<;> rw[h]<;>simp)]
       obtain ⟨b,hB,h3,h4⟩:= glows i s hs; rw [h2,h3,sense,senseL,polar,polar,if_neg hu,if_neg (show insert i s≠t from ?_),mul_zero,mul_zero]; intro h; exact hu (by unfold u; rw [←h, Finset.erase_insert hs])
     rw[hush _ _ he]; by_cases ht:i∈s; · rw[ash _ _ ht]; simp [poly]
     obtain ⟨a,hb,h1,h2⟩:=glows i s ht; rw [h1,senseL,polar,if_neg (show insert i s≠ t from fun h=>he (h ▸ Finset.mem_insert_self ..)),mul_zero]; simp[poly]
lemma celebrates(x y:Alg X):poly (atom i*x) y= poly x (vary i y):=by
    rw [← write x, ← write y]; simp_rw [mul_sum,map_sum,lunarL]; apply sum_congr rfl; intro j _; simp_rw[lunar]; refine sum_congr rfl fun k _=>?_; rw [mul_smul_comm, map_smul,senseL,sense,senseL,sense,creating]
-- substitutions. premise generator-unit.
variable [DecidableEq X]
variable (S:Matrix X X ℂ)(hS:S∈unitary _)(x y:Alg X)
omit hS
lemma changed (s:Finset X):changeVars S (mono s)∈ layer X s.card:=by
     obtain ⟨f,-,_,hf⟩:=expression s
     have hh(l:List X):changeVars S (l.map atom).prod∈ layer X l.length:=by
             induction l with
             | nil=> simp
             | cons p l ih=>simp only[List.map_cons,List.prod_cons,map_mul,change_atom,List.length_cons]; rw [add_comm]; refine layer_mul (?_ : _ ∈layer X 1) ih; exact (layer X 1).sum_mem fun i _=> (layer X 1).smul_mem _ (atom_mem _)
     rw [hf]; simpa only [List.map_ofFn, List.length_ofFn] using hh (List.ofFn f)
include hS
lemma saturates : poly (changeVars S x) (changeVars S y)=poly x y:=by
     let X0:=changeVars S
     have hf(Z:List X)(y:Alg X): poly (X0 ((Z.map atom).prod)) (X0 y)=poly (Z.map atom).prod y:=by
           induction Z generalizing y with
           | nil=> rw [← write y,map_sum,List.map_nil,List.prod_nil,map_one,← mono_empty,core,core,map_sum, map_sum]
                   apply Finset.sum_congr rfl; intro j _; rw [map_smul,map_smul,map_smul]; by_cases h:j=∅; · rw [h,mono_empty,map_one]
                   rw [Grass.read_other _ _ (Ne.symm h),spectrum (changed ..) ∅ (by simp [h,eq_comm])] -- syntax
           | cons i l ih=>
              let u:= (l.map atom).prod
              change poly (X0 (atom i*u)) (X0 y)=_
              have he(k:X) : ∑ j:X, star (S i j) * S k j=(1:Matrix X X ℂ) k i:=by
                      have h:= congr_fun (congr_fun hS.2 k) i; simp only [Matrix.mul_apply] at h; exact (Finset.sum_congr rfl fun j _=> mul_comm ..).trans h -- numerator.
              have ha : ∑ j:X, (star (S i j)) • vary j (X0 y)=X0 (vary i y):=by
                      unfold X0; simp_rw [Sway.chain,Finset.smul_sum,smul_smul]; rw[sum_comm,Finset.sum_eq_single i]; · rw [← Finset.sum_smul,he, Matrix.one_apply_eq,one_smul]
                      · intro j _ h; rw [← Finset.sum_smul,he, Matrix.one_apply_ne h,zero_smul]
                      simp
              unfold X0 at *
              rw [map_mul,change_atom,sum_mul,lunarL]; simp only[List.map_cons,List.prod_cons, celebrates,smul_mul_assoc,senseL] -- creates
              rw [← ih]; rw[← ha]; simp_rw [lunar,sense] -- limb. check
              rfl
     conv_lhs => rw[← write x,map_sum]
     conv_rhs => rw[← write x]
     rw[lunarL,lunarL]; refine sum_congr rfl fun i _=>?_ ; rw [map_smul,senseL,senseL]; obtain ⟨f,-,_,he⟩:=expression i; congr 1; rw [he]; simpa only[List.map_ofFn] using hf (List.ofFn f) y
end YM.Sprig.Chloe
#print axioms YM.Sprig.Chloe.saturates
#print axioms YM.Sprig.Chloe.onlyH
