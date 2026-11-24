import YM.Mako.Lips
set_option autoImplicit false
noncomputable section
namespace YM.Mako
open Set Function Filter Polynomial LinearMap Module
open scoped Topology BigOperators Classical
variable {W:Type*}[AddCommGroup W][Module ℂ W][FiniteDimensional ℂ W]
local notation "M"=> Module.End ℂ W
variable {C:Set (Module.End ℂ W)} {f g:Module.End ℂ W}
/-- Non-unital span of ordered words; certificates with positive length. -/
inductive Fet (C:Set (Module.End ℂ W)): (Module.End ℂ W)→Prop
   | mem (x:M): x∈C→ Fet C x
   | zero : Fet C 0
   | times (x y:M): Fet C x→ Fet C y→Fet C (x*y)
   | add(x y:M):Fet C x→Fet C y→Fet C (x+y)
   | smul(a:ℂ)(x:M): Fet C x→ Fet C (a • x)
namespace Fet
lemma neg(H:Fet C f): Fet C (-f):=neg_one_smul ℂ f ▸ smul _ _ H
lemma sub(H:Fet C f)(h:Fet C g): Fet C (f-g):=by rw[sub_eq_add_neg]; exact Fet.add _ _ H (Fet.neg h) -- arg order
lemma pow'(H:Fet C f)(n:ℕ): Fet C (f^(n+1)):=by
     induction n with
     | zero=> simpa using H
     | succ n ih=> rw[pow_succ]; exact times _ _ ih H -- parse
lemma eval (H:Fet C f)(P:Polynomial ℂ):Fet C (f*aeval f P):=by
     induction P using Polynomial.induction_on' with
     | add p q h₁ h₂=> rw[_root_.map_add,mul_add]; exact add _ _ h₁ h₂
     | monomial n a=> rw [←C_mul_X_pow_eq_monomial,_root_.map_mul,_root_.map_pow,aeval_C,aeval_X,algebraMap_end_eq_smul_id]; change Fet C (f*(a • (1:M)*f^n)); rw [smul_mul_assoc,one_mul,mul_smul_comm,←pow_succ']; exact smul _ _ (H.pow' n)
lemma pose(H:Fet C f)(p:Lace f): Fet C (aeval f p.poly-1):=by
    obtain ⟨q,hq⟩:= Polynomial.X_dvd_sub_C (p:=p.poly); rw[coeff_zero_eq_eval_zero,p.root,_root_.map_one] at hq; rw [← show aeval f (1:Polynomial ℂ) = (1:M) from (_root_.map_one ..), ← _root_.map_sub,hq,_root_.map_mul,aeval_X]; exact eval H q
lemma mono (h:Fet C f){D:Set M}(hx:C⊆D): Fet D f:=by
     induction h with
     | mem i h=> exact mem i (hx h)
     | zero=> exact zero
     | times x y _ _ ih h=> exact times _ _ ih h
     | add x y _ _ ih h=> exact add _ _ ih h
     | smul a x _ h=> exact smul _ _ h
lemma products (hf:Fet C (f-1))(hg:Fet C (g-1)):Fet C (f*g-1):=by
     rw[show f*g-1=(f-1)*(g-1)+(f-1)+(g-1) from (by noncomm_ring)]; exact add _ _ (add _ _ (times _ _ hf hg) hf) hg
lemma comm(H:Fet C f)(hx:∀ x∈C,Commute g x):Commute g f:=by
     induction H with
     | mem i h=>exact hx i h
     | zero=>exact Commute.zero_right _
     | times p q _ _ h h'=>exact h.mul_right h'
     | add p q _ _ h h'=>exact h.add_right h'
     | smul a x _ h=>exact h.smul_right _
lemma stamp(H:Fet C (f-1))(hx:∀ x∈C,Commute g x): Commute g f:=by
     have he:= (comm H hx).add_right (Commute.one_right _); rwa [sub_add_cancel] at he
lemma hits(U:Submodule ℂ W)(x:W)(H:Fet C f)(h:∀ p∈C,∀ y:W,p y∈ U): f x∈ U:=by
     induction H generalizing x with
     | mem i hi=>exact h i hi x
     | zero=>exact U.zero_mem
     | times p q _ _ hp _=>exact hp (q x)
     | add p q _ _ hp hq=> exact U.add_mem (hp x) (hq x)
     | smul a p _ hp=> exact U.smul_mem _ (hp _)
lemma static(H:Fet C f)(x:W)(h:∀ p∈C,p x=0): f x=0:=by
    induction H with
    | mem i hi=>exact h i hi
    | zero=>rfl
    | times p q _ _ _ h=> rw[End.mul_apply,h,_root_.map_zero]
    | add p q _ _ h h' => rw[LinearMap.add_apply,h,h',add_zero]
    | smul a p _ h=> rw[LinearMap.smul_apply,h,smul_zero]
lemma identity(H:Fet C (f-1))(x:W)(h:∀ p∈C,p x=0): f x=x:= sub_eq_zero.mp (H.static x h)
end Fet
structure Split (f:End ℂ W)(C:Set (End ℂ W)):Prop where
     hit (x:End ℂ W)(h:x∈C) : x*f=0 -- syntax
     gun (x:End ℂ W)(h:x∈C) : f*x=0
     budget : Fet C (f-1)
end YM.Mako
#print axioms YM.Mako.Fet.pose
#print axioms YM.Mako.Fet.pow'
#print axioms YM.Mako.Fet.stamp
#print axioms YM.Mako.Fet.identity
#print axioms YM.Mako.Fet.hits
#print axioms YM.Mako.Fet.sub
#print axioms YM.Mako.Fet.mono
