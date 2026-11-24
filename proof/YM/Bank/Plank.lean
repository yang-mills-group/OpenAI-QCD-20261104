import YM.Bank.Peak
import YM.Maxwell.Curls
import YM.Massive.Target.Wick
set_option autoImplicit false
noncomputable section
namespace YM.Bank.Plank
open Function Precision Laurent Bloch Metric Gauge Wilson RG Finset Filter Lattice Exterior Next.Free
open Glyph Palm Jule Kith Peak Osc Pilot Bee Wale Analysis Maxwell
open scoped Topology Matrix Matrix.Norms.L2Operator ContDiff BigOperators ComplexConjugate
variable {f g F G : E4→ℂ} {k n:ℕ}
-- fork certificate
structure Flute (f:Momentum→ℂ)(g:E4→ℂ)(k:ℕ): Prop where
   song: ∃ L:recordL, steady L k ∧ (∀ x:Momentum, physical x→f x=crewG L x) ∧ (∀ x:E4,x ≠0→g x=metricL L x)
attribute [local simp] Complex.real_smul
namespace Flute
variable {a b:Momentum→ℂ}
def sumA (L:recordL)(W:List Axis →ℂ):= ∑ i∈L.support,L i*W i
lemma soundW (L:recordL)(S:Finset (List Axis))(hs:L.support⊆S) (W:List Axis→ℂ):sumA L W= ∑ i∈S,L i*W i:=sum_subset hs (fun _ _ h=> by rw [Finsupp.notMem_support_iff.mp h, zero_mul])
lemma sumM (L K:recordL)(W:List Axis→ℂ) : sumA (L+K) W=sumA L W+sumA K W:=by
    classical
    rw [soundW _ _ Finsupp.support_add,soundW L (L.support∪K.support) subset_union_left,soundW K (L.support∪K.support) subset_union_right,← sum_add_distrib]; simp only [Finsupp.add_apply,add_mul]
lemma sumS (L:recordL)(W:List Axis→ℂ)(c:ℂ): sumA (c • L) W=c*sumA L W:=by rw [soundW _ L.support Finsupp.support_smul, sumA,mul_sum]; apply sum_congr rfl; intro i _; rw [Finsupp.smul_apply,smul_eq_mul,mul_assoc]
lemma sumF (i:List Axis)(W:List Axis→ℂ):sumA (Finsupp.single i 1) W=W i:=by simp [sumA]
lemma empty : Flute 0 0 k:=by refine ⟨0,?_,?_,?_⟩; all_goals simp [steady,crewG,metricL]
lemma ful (l:List Axis)(hp:l.length=k+1): Flute (Bee.field l) (current l) k:=by
    refine ⟨Finsupp.single l 1, ?_,fun x h=> (sumF l (fun i=>Bee.field i x)).symm,fun x h=>(sumF l (fun i=> current i x)).symm⟩; intro i hi; simp at hi; rw [hi,hp]
lemma add (X:Flute a f k)(Y:Flute b g k):Flute (a+b) (f+g) k:=by
    obtain ⟨L,H,h,h₀⟩:=X; obtain ⟨M,Q,y,k⟩:=Y
    refine ⟨L+M,fun i hi=> ((mem_union.mp (Finsupp.support_add hi)).elim (H i) (Q i)), fun p hp=> ?_,fun x hx=>?_⟩
    · rw [Pi.add_apply,h p hp,y p hp]; exact (sumM L M fun i=> Bee.field i p).symm
    rw [Pi.add_apply,h₀ x hx,k x hx]; exact (sumM L M fun i=> current i x).symm
lemma scale (X:Flute a f k)(t:ℂ):Flute (t • a) (t • f) k:=by
    obtain ⟨L,H,h,h₀⟩:=X
    refine ⟨t • L,fun i hi=> H i (Finsupp.support_smul hi), fun p hp=>?_,fun x hx=>?_⟩
    · rw [Pi.smul_apply,h p hp]; exact (sumS L (fun i=> Bee.field i p) t).symm
    rw [Pi.smul_apply,h₀ x hx]; exact (sumS L (fun i=>current i x) t).symm
lemma neg (X:Flute a f k): Flute (-a) (-f) k:=by simpa using X.scale (-1)
lemma sub (X:Flute a f k)(Y:Flute b g k):Flute (a-b) (f-g) k:=by simpa [sub_eq_add_neg] using X.add Y.neg
lemma fiat (X:Flute a f k){Y:Momentum→ℂ}{g:E4→ℂ} (h:∀ p,physical p→Y p=a p)(hx:∀ x:E4,x≠0→ g x=f x):Flute Y g k:=by obtain ⟨L,H,hH,h₀⟩:=X; exact ⟨L,H,fun p hp=> (h p hp).trans (hH p hp),fun p hp=> (hx p hp).trans (h₀ p hp)⟩
lemma tall {m:Type}(s:Finset m) (f:m→Momentum→ℂ)(g:m→E4→ℂ)(h:∀ i∈s,Flute (f i) (g i) k): Flute (∑ i∈s,f i) (∑ i∈s,g i) k:=by classical induction s using Finset.induction_on with
    | empty=> simp; exact empty
    | insert i s hi ih=> rw [sum_insert hi,sum_insert hi]; exact (h i (mem_insert_self ..)).add (ih fun q hq=> h q (by simp[hq]))
open Complex (I)
lemma fun_m (a:Axis){f':Momentum→ℂ}(X:Flute f' f k) : Flute (fun p=> I*p a*f' p) (Analysis.D (basis a) f) (k+1):=by -- implicit
    obtain ⟨L,H,h,h₀⟩:=X
    let Y (l:List Axis) := L l • Bee.field (a::l); let F (l: List Axis):= L l • current (a::l)
    apply Flute.fiat (Flute.tall L.support Y F (fun l hl=> (ful (a::l) (by simp[H l hl])).scale (L l)))
    · intro p hp; rw [h p hp]; unfold crewG; rw [mul_sum,Finset.sum_apply]; apply sum_congr rfl; intro i _; change _= L i * ((axle p)⁻¹ * (I*p a* barrier p i)); unfold Bee.field; ring
    intro x hx
    have he:= (Analysis.GermD (basis a) (show f=ᶠ[𝓝 x] metricL L from Eventually.mono (open_away.mem_nhds hx) (fun y hy=> h₀ y hy)))
    rw [he, Finset.sum_apply]; unfold Analysis.D metricL
    have hs l:DifferentiableAt ℝ (current l) x:=(Ecore l (Complex.ofRealCLM.contDiff.contDiffAt.comp x (freeSmooth hx))).differentiableAt (by simp)
    rw [fderiv_fun_sum (fun i _ => (hs i).const_mul _),_root_.sum_apply]; refine sum_congr rfl fun i _=> ?_
    rw [fderiv_const_mul (hs i)]; rfl
lemma functions (u v:List Axis){A:Momentum→ℂ}(X:Flute A f k): Flute (spinJet u v A) ((-1:ℂ)^v.length • earn v (earn u f)) (k+u.length+v.length):=by
    have hx(u:List Axis):Flute (fun p=>A p*barrier p u) (earn u f) (k+u.length):=by
         induction u with
         | nil=>simpa [earn,barrier] using X -- check
         | cons i l ih=> simpa [spinJet,barrier,add_assoc,mul_left_comm,mul_assoc,earn] using fun_m i ih
    induction v with
    | nil=> rw [show spinJet u [] A=(fun p=> A p*barrier p u) from funext fun p=>by simp [spinJet,barrier]]; simpa only [earn,List.foldr_nil,List.length_nil,pow_zero,one_smul,Nat.add_zero] using hx u
    | cons i l ih=>
       have h₀:= fun_m i ih
       rw [List.length_cons,← Nat.add_assoc]; refine h₀.neg.fiat (fun p hp=> ?_) (fun x hp=>?_)
       · unfold spinJet; change _= -(I * p i*(A p* barrier p u*barrier (-p) l)); simp [spinJet,barrier]; ring
       have hf : ContDiffAt ℝ ∞ f x:=by
          obtain ⟨L,H,h,h₀⟩:=X
          have hv : ContDiffAt ℝ ∞ (metricL L) x:= ContDiffAt.sum fun i _=> contDiffAt_const.mul (Ecore i (Complex.ofRealCLM.contDiff.contDiffAt.comp _ (freeSmooth hp)))
          exact hv.congr_of_eventuallyEq (Eventually.mono (open_away.mem_nhds hp) fun y hy=> h₀ y hy)
       let Z:=earn l (earn u f)
       have ht:= Ecore l (Ecore u hf)
       unfold Analysis.D; change _ * fderiv ℝ Z x (basis i) = -(fderiv ℝ (((-1:ℂ)^l.length) • Z) x (basis i))
       rw [fderiv_const_smul (ht.differentiableAt (by simp)),pow_succ (-1:ℂ)]; simp [Z]
end Flute
end YM.Bank.Plank
#print axioms YM.Bank.Plank.Flute.functions
