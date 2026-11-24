import YM.QCD.Brick.Panel
import YM.QCD.Pearl.Spring
/-! # Lifted row fields with derivative displacement price -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Brick
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open Garden Fork Leaf Tee Flume YM.Next.Free Laurent
variable {c f:Side} {j k N m:ℕ}(B:Plan j)(F:Flight j k) (h:f.val=c.val*F.L.val){p r q t :ℝ}
set_option quotPrecheck false
section latent
variable {D:Type*} [Fintype D]{Z:D→ℕ}
def gust (Y:Cover→Alg D) (a:Axis)(x:Cover):=Y (x+step a)-Y x
def affineD (Y:Axis→ Alg D)(x:Cover):=∑ i, (x i:ℂ) • Y i
lemma forwardH (Y:Axis→Alg D)(x:Cover)(i:Axis): affineD Y (x+step i)-affineD Y x=Y i:=by
   unfold affineD; rw [← Finset.sum_sub_distrib,sum_eq_single i]
   · simp [Lattice.step,add_smul]
   · intro j _ hj; simp [Lattice.step,hj,hj.symm]
   simp
lemma stepQ (M:ℕ)(x:Cover)(l:Walk)(p : ℝ)(X:Cover→ Alg D)(he:∀ a x, size x ≤ M→ size (x+step a) ≤ M→ visc Z t (gust X a x) ≤ p)(ht:size x +l.length ≤ M) : visc Z t (X (stop x l)-X x) ≤ l.length*p:=by
   induction l generalizing x with
   | nil=> simp only [stop,List.length_nil,Nat.cast_zero,zero_mul,sub_self, visc,map_zero,norm_zero,le_refl]
   | cons a l ih=>
     let y: Cover := x+a.vec; have hy:size y ≤ size x+1:= by exact Pearl.stepStop x [a]
     simp only [List.length_cons] at ht ⊢; have hx:= ih y (by omega); have hv : visc Z t (X y-X x)≤p:=by
       cases a with |mk a b =>
         cases b
         · exact he _ _ (show size x≤M by omega) (hy.trans (by omega))
         change visc Z t (X (x+ -step a)- X x)≤p; rw [visc,map_sub,norm_sub_rev,←map_sub]; have hg:= he a (x+ -step a) (show size (x+-step a)≤M from hy.trans (by omega)) (by rw [neg_add_cancel_right]; omega); unfold gust at hg; simpa only [neg_add_cancel_right,visc] using hg
     rw [show stop x _=stop y l from rfl]; rw [show X (stop y l)-X x=(X (stop y l)-X y)+(X y-X x) by abel]
     exact (vested ..).trans ((add_le_add hx hv).trans_eq (by push_cast; ring))
lemma walkQ (A:Cover)(v:ℕ)(ht:size A≤v)(X: Cover→ Alg D)(hf:∀ i x,size x≤v→ size (x+step i)≤v→ visc Z t (gust X i x) ≤ p): visc Z t (X A-X 0) ≤ size A*p:=by
   let w:= route 0 A 1; have hp:w.length=size A:= by rw [show w= _ from rfl,Extra.Iteration.route_length,sub_zero] -- edit
   have hh:= stepQ v 0 w _ X hf (show size (0:Cover)+w.length≤ v by simpa [Laurent.size,hp] using ht); rwa [show stop 0 w=A from route_end .., hp] at hh
@[simp] lemma affine_null (X:Axis→Alg D): affineD X 0=0:=by simp [affineD]
lemma safari (A:Cover)(v:ℕ)(ht:size A≤v)(X : Cover→Alg D)(hf:∀ i j x,size x≤ v → visc Z t (gust (gust X i) j x) ≤ p) (hp:0≤p): visc Z t (X A-X 0-affineD (fun i=>gust X i 0) A) ≤ v^2*p:=by
    let Y:=affineD fun i=> gust X i 0; let H (x:Cover):=X x-Y x
    have hj(i:Axis)(x:Cover): gust H i x=gust X i x - gust X i 0:=by have h:= forwardH (D:=D) (fun i=> gust X i 0) x i; change _ - _ =_ at h; unfold gust H Y; rw [sub_sub_sub_comm, h]; rfl
    have h:visc Z t (H A-H 0) ≤ size A*(v*p):= walkQ A v ht H fun i x he _=>by
       rw [hj]; exact (walkQ _ v he (gust X i) (fun j x hv _=> hf _ _ _ hv)).trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr he) hp)
    rw [show H A-H 0=X A-X 0-Y A from ?_] at h; swap; · unfold H; rw [show Y 0=0 from affine_null _,sub_zero]; abel
    apply h.trans; exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr ht) (mul_nonneg (Nat.cast_nonneg (α:=ℝ) v) hp)).trans_eq (by ring) -- nat pow V^2 issue
lemma valAffine (X:Axis→Alg D)(x:Cover)(hp:∀ i, visc Z t (X i) ≤ p): visc Z t (affineD X x) ≤ size x * p:=by
    refine (vc_sum ..).trans ((sum_le_sum (g:=fun i => ((x i).natAbs:ℝ)*p) fun i _=>?_).trans ?_)
    · rw [vc_scale,show ‖(↑(x i):ℂ)‖=((x i).natAbs:ℝ) by simp]; exact mul_le_mul_of_nonneg_left (hp i) (Nat.cast_nonneg _)
    unfold Laurent.size; rw [← Finset.sum_mul, Nat.cast_sum]
end latent
lemma travelT (i j:Site c)(s: Finset (Keys c N)) : pieD (Stew.lens i) s ≤ (1+separation j i)^2*pieD (Stew.lens j) s:=by
    unfold pieD; rw [← mul_pow]; apply Nat.pow_le_pow_left
    suffices s.sup (Stew.lens i) ≤ s.sup (Stew.lens j)+separation j i by nlinarith only [this]
    apply Finset.sup_le; intro k hk; exact (separation_triangle (locationP k) j i).trans (Nat.add_le_add_right (le_sup hk (f:=Stew.lens j)) (separation j i))
lemma trails (i j:Site c)(X: Alg (Keys c N))(ht:0 ≤ t) : Stew.plank i t X ≤ (1+(separation j i:ℝ))^2*Stew.plank j t X:=by
   unfold Stew.plank; rw [pricesD _ ht,pricesD _ ht, Finset.mul_sum]; apply sum_le_sum; intro x hx
   simp only [starch]; rw [← mul_assoc (a:=(1+(separation j i:ℝ))^2), ← mul_assoc (a:=(1+(separation j i:ℝ))^2)]; gcongr (?_:ℝ)*_*_; -- placeholder
   exact_mod_cast travelT i j x
end YM.QCD.Brick
