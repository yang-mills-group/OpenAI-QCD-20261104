import YM.QCD.Globe.Fife
import YM.QCD.Brick.Perk
import YM.QCD.Nola.Wheat
import YM.QCD.Nola.Arch
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Globe
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden Entr Kites
variable {f c:Side}{j k m N:ℕ}{S:Flight j k} {h:f.val=c.val*S.L.val}{p:BudgetPoint}
open Fork
variable (S h)
-- affine estimate in a weighted row space (fixed outer vertex). scalar action.Uniform any moment >=2
set_option quotPrecheck false
abbrev Alder (c:Side):= Site c→Lat.Bundle
noncomputable def fir (p:Site c)(m:ℕ)(X:Alder c):ℝ:= ∑ i,costS m p i* ‖X i‖
lemma fir_t (X Y:Alder c)(p: Site c): fir p m (X+Y) ≤ fir p m X+ fir p m Y:=by unfold fir; rw [← sum_add_distrib]; apply sum_le_sum; intro i _; rw [← mul_add]; exact mul_le_mul_of_nonneg_left (norm_add_le (X i) (Y i)) (cost_nn ..)
lemma fir_s (X:Alder c)(b:ℂ)(p: Site c): fir p m (b • X)=‖b‖*fir p m X:=by unfold fir; rw [mul_sum]; refine sum_congr rfl fun i _=>?_ ; rw [Pi.smul_apply,norm_smul, mul_left_comm]
@[simp] lemma fir_n (p:Site c)(X:Alder c):fir p m (-X)=fir p m X:=by rw [← neg_one_smul ℂ, fir_s, norm_neg, norm_one,one_mul]
lemma fir_h (X Y:Alder c)(p:Site c):fir p m (X-Y)≤ fir p m X+fir p m Y:=by
    rw [sub_eq_add_neg,← fir_n p Y]; -- changes lhs Y? targets inspect
    exact fir_t _ _ _
lemma fir_l (X:Alder c)(p:Site c)(F: Bundle): fir p m (fun i=> F*X i) ≤ ‖F‖*fir p m X:=by unfold fir; rw [mul_sum]; refine sum_le_sum fun i _=>?_ ; rw [mul_left_comm (‖F‖)]; exact mul_le_mul_of_nonneg_left (norm_mul_le F (X i)) (cost_nn ..)
@[simp] lemma fir0 (p:Site c):fir p m 0=0:=by unfold fir; simp
lemma fir_sum {D:Type*}(p:Site c)(X:D→Alder c)(s: Finset D): fir p m (∑ i∈s,X i) ≤∑ i∈s,fir p m (X i):=by induction s using Finset.induction_on with
   | empty=>simp
   | insert a s ha ih=> rw [sum_insert ha, sum_insert ha]; exact (fir_t ..).trans (add_le_add_right ih _) -- add side
lemma fir_rot (p q:Site c)(X:Alder c): fir p m X ≤ costS m p q*fir q m X:=by unfold fir; rw [mul_sum]; refine sum_le_sum fun i _=>?_ ; rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (cost_b p q i) (norm_nonneg _)
variable {L:ℕ}
lemma rel (r:Ratio c f)(o:Site f)(v:Cover)(hv:Laurent.size v ≤ L): costS m (r.parent o) (r.parent (o+wrap _ v))≤ (2+(L:ℝ)*(r.count.val:ℝ)⁻¹)^m:=by
    unfold costS; apply pow_le_pow_left₀ (by positivity); have he:= Brick.citizen (R:=r) o v L hv; rw [separation_comm] at he; have hp:=sq_nonneg (↑(L):ℝ); nlinarith [Nat.cast_nonneg (α:=ℝ) (separation (r.parent o) (r.parent (o+wrap _ v))), mul_nonneg (Nat.cast_nonneg (α:=ℝ) L) (show 0 ≤ (r.count.val:ℝ)⁻¹ by positivity)]
open Laurent
-- site norm on jets bundled; reuse structure
lemma percept (r:Ratio c f)(v:Cover)(Y: Kit.Rail f c)(o:Site f)(ht:size v≤ L){t:ℝ}(he: Cent r.parent id m t Y):fir (r.parent o) m (fun i=> cell Y (o+wrap _ v) i)≤ (2+(L:ℝ)*(r.count.val:ℝ)⁻¹)^m*t:=by
    apply (fir_rot _ (r.parent (o+wrap _ v)) _).trans; exact mul_le_mul (rel r o v ht) (he _) (sum_nonneg fun _ _=>mul_nonneg (cost_nn ..) (norm_nonneg _)) (by positivity)
-- elementary Taylor 
variable (o: Site c)
def stepA (a:Axis)(X:Cover→Alder c):Cover→ Alder c:= fun p=> X (p+step a)-X p
def firstA (v:Cover)(X:Cover→ Alder c):= ∑ a:Axis, (v a:ℂ) • stepA a X 0
lemma firstup (X:Cover→ Alder c)(v:Cover)(a:Axis):firstA (v+step a) X-firstA v X=stepA a X 0:=by
    unfold firstA; rw [← Finset.sum_sub_distrib,sum_eq_single a]
    · simp [Lattice.step,add_smul]
    · intro j _ hj; simp [Lattice.step,hj,hj.symm]
    simp
variable {t:ℝ}
lemma padQ (M:ℕ)(x:Cover)(l:Lattice.Walk)(X:Cover→Alder c)(he:∀ a x,size x ≤ M→size (x+step a)≤M→ fir o m (stepA a X x)≤t)(ht:size x+l.length ≤ M) : fir o m (X (stop x l)-X x) ≤ l.length*t:=by
   induction l generalizing x with
   | nil=> simp only [stop,List.length_nil,Nat.cast_zero,zero_mul,sub_self, fir0,le_refl]
   | cons a l ih=>
     let y: Cover := x+a.vec; have hy:size y ≤ size x+1:= by exact Pearl.stepStop x [a]
     simp only [List.length_cons] at ht ⊢; have hx:= ih y (by omega); have hv : fir o m (X y-X x)≤t:=by
       cases a with |mk a b =>
         cases b
         · exact he _ _ (show size x≤M by omega) (hy.trans (by omega))
         have hh:x+(-step a:Cover)+step a=x:=by abel
         have he': y=(x+-step a):=rfl
         have hq := he a y (hy.trans (by omega)) (by rw [he',hh]; omega); unfold stepA at hq; rw [show y+step a=x from by rw [he',hh]] at hq -- fix
         rw [← fir_n _ (X y-X x), neg_sub]; exact hq
     rw [show stop x _=stop y l from rfl]; rw [show X (stop y l)-X x=(X (stop y l)-X y)+(X y-X x) by abel]
     exact (fir_t ..).trans ((add_le_add hx hv).trans_eq (by push_cast; ring))
lemma routeA (A:Cover)(v:ℕ)(ht:size A≤v)(X: Cover→ Alder c)(hf:∀ i x,size x≤v→ size (x+step i)≤v→ fir o m (stepA i X x) ≤ t): fir o m (X A-X 0) ≤ size A*t:=by
   let w:= route 0 A 1; have hp:w.length=size A:= by rw [show w= _ from rfl,Extra.Iteration.route_length,sub_zero]
   have hh:= padQ o v 0 w X hf (show size (0:Cover)+w.length≤ v by simpa [Laurent.size,hp] using ht); rwa [show stop 0 w=A from route_end .., hp] at hh
@[simp] lemma first_nil (X:Cover→ Alder c): firstA 0 X=0:=by simp[firstA]
lemma firstH (A:Cover)(v:ℕ)(ht:size A≤v)(X : Cover→ Alder c)(hf:∀ i j x,size x≤ v → fir o m (stepA j (stepA i X) x) ≤ t) (hp:0≤t): fir o m (X A-X 0-firstA A X) ≤ v^2*t:=by
    let Y:= fun z=> firstA z X; let H (x:Cover):=X x-Y x
    have hj(i:Axis)(x:Cover): stepA i H x=stepA i X x - stepA i X 0:=by unfold stepA H Y; rw [sub_sub_sub_comm, firstup]; rfl
    have h:fir o m (H A-H 0) ≤ size A*(v*t):= routeA o A v ht H fun i x he _=>by
       rw [hj]; exact (routeA _ _ v he (stepA i X) (fun j x hv _=> hf _ _ _ hv)).trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr he) hp)
    rw [show H A-H 0=X A-X 0-Y A from ?_] at h; swap; · unfold H; rw [show Y 0=0 from first_nil _,sub_zero]; abel
    apply h.trans; exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr ht) (mul_nonneg (Nat.cast_nonneg (α:=ℝ) v) hp)).trans_eq (by ring)
lemma first_bill (X: Cover→ Alder c)(hp:∀ i, fir o m (stepA i X 0) ≤ t)(A:Cover): fir o m (firstA A X) ≤ size A*t:=by
    apply (fir_sum ..).trans; unfold Laurent.size; rw [Nat.cast_sum,sum_mul]; refine sum_le_sum fun i _=>?_ ; rw [fir_s,show ‖(↑(A i):ℂ)‖=(↑(A i).natAbs:ℝ) by simp]; exact mul_le_mul_of_nonneg_left (hp i) (Nat.cast_nonneg _)
end YM.QCD.Globe
