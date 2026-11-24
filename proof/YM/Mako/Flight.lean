import YM.Mako.Arum
set_option maxHeartbeats 500000
set_option autoImplicit false
noncomputable section
namespace YM.Mako
open Function Filter Set
open scoped Topology Classical BigOperators
open Module Polynomial
variable {W V:Type*} [AddCommGroup W][Module ℂ W][FiniteDimensional ℂ W]
variable [AddCommGroup V][Module ℂ V][FiniteDimensional ℂ V]
local notation "M"=> W →ₗ[ℂ] V
-- commutator
noncomputable def power (P:End ℂ W)(Q:End ℂ V):End ℂ (W→ₗ[ℂ]V):=
    { toFun f:= Q ∘ₗ f - f ∘ₗ P
      map_add' x y:= by ext1 i; simp only [LinearMap.add_apply,LinearMap.sub_apply, LinearMap.comp_apply,map_add]; abel
      map_smul' a v:=by ext1 i; simp [smul_sub] }
variable (p q:End ℂ W) (P Q:End ℂ V)
lemma power_app(v: M) (x:W): power p P v x=P (v x)-v (p x):=rfl
lemma power_bracket : clip (power p P) (power q Q)=power (clip p q) (clip P Q):=by
     apply LinearMap.ext; intro f; apply LinearMap.ext; intro x; simp only[clip,LinearMap.sub_apply,End.mul_apply,power_app,map_sub]; abel
lemma power_add : power (p+q) (P+Q)=power p P+power q Q:=by
     apply LinearMap.ext; intro f; apply LinearMap.ext; intro x; simp only[LinearMap.add_apply,power_app,map_add]; abel
lemma power_smul(r:ℂ):power (r • p) (r • P)=r • power p P:=by apply LinearMap.ext; intro f; apply LinearMap.ext; intro x; simp only[LinearMap.smul_apply,power_app,map_smul,smul_sub]
-- power semisimple follows because left/right actions individually inherit minpoly. right is anti-hom, prove powers evaluate. 
noncomputable def lip (Q: End ℂ V):End ℂ (W→ₗ[ℂ]V):= power 0 Q
noncomputable def lad(p: End ℂ W):End ℂ (W→ₗ[ℂ]V):= power (-p) 0
lemma lip_y(v: M): lip Q v= Q ∘ₗ v:= LinearMap.ext (fun i=>by unfold lip; rw [power_app]; simp)
lemma lad_y(v:M): lad p v= v ∘ₗ p:= LinearMap.ext (fun i=>by unfold lad; rw[power_app]; simp)
lemma ell (Q1:Polynomial ℂ)(v:M)(x:W): aeval (lip Q) Q1 v x = aeval Q Q1 (v x):=by
     have hp(n:ℕ): ((lip Q)^n) v x= (Q^n) (v x):=by
           induction n with
           | zero=>simp
           | succ n h=> rw [pow_succ', End.mul_apply,lip_y,LinearMap.comp_apply,h,pow_succ',End.mul_apply]
     induction Q1 using Polynomial.induction_on' with
     | add p q h h'=>rw [map_add, map_add,LinearMap.add_apply,LinearMap.add_apply,LinearMap.add_apply,h,h']
     | monomial n a=> rw [← C_mul_X_pow_eq_monomial]; simp [algebraMap_end_apply,hp]
lemma lick (Q1:Polynomial ℂ)(v:M)(x:W): aeval (lad p) Q1 v x = v (aeval p Q1 x):=by
     have hp(n:ℕ):∀ x:W, ((lad p)^n) v x= v ((p^n) x):=by
           induction n with
           | zero=> simp
           | succ n h=> intro i; rw [pow_succ',End.mul_apply,lad_y,LinearMap.comp_apply,h,pow_succ p,End.mul_apply]
     induction Q1 using Polynomial.induction_on' with
     | add p q h h'=>rw [map_add,map_add,LinearMap.add_apply,LinearMap.add_apply,LinearMap.add_apply,map_add,h,h']
     | monomial n a=> rw [←C_mul_X_pow_eq_monomial]; simp [algebraMap_end_apply,hp]
lemma step (hp:p.IsSemisimple)(hQ:Q.IsSemisimple): (power p Q).IsSemisimple:=by
     have hx:End.IsSemisimple (lip (W:=W) Q) := End.isSemisimple_of_squarefree_aeval_eq_zero hQ.minpoly_squarefree (LinearMap.ext (fun f=>LinearMap.ext fun i=> (ell Q _ f i).trans (by rw[minpoly.aeval]; rfl)))
     have hg:End.IsSemisimple (lad (V:=V) p):=End.isSemisimple_of_squarefree_aeval_eq_zero hp.minpoly_squarefree (LinearMap.ext (fun f=>LinearMap.ext fun i=> (lick p _ f i).trans (by rw[minpoly.aeval,LinearMap.zero_apply,map_zero]; rfl)))
     rw[show power p Q= lip Q-lad p from (by apply LinearMap.ext; intro x; rw [LinearMap.sub_apply,lip_y,lad_y]; rfl)]; exact hx.sub_of_commute (show Commute (lip (W:=W) Q) (lad p) from LinearMap.ext (fun x=>by rw [End.mul_apply,End.mul_apply,lad_y, lip_y, lip_y,lad_y]; rfl)) hg
end YM.Mako
#print axioms YM.Mako.step
#print axioms YM.Mako.power_bracket
#print axioms YM.Mako.power_smul
#print axioms YM.Mako.power_add
