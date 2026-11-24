import YM.Lapin.Kroft
import YM.Clink.Mote
/-! Neighbor row upper U-component cost.G links no physical approximation.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Massive.Patria.Gall.Cahoots
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical Kronecker InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
open Tawny Tawny.Cast Tawny.Cast.Rays
variable {C:ℝ}{c:Side}{n l d m r k p q w i N:ℕ}{U:BudgetPoint}
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas PCAC Patria Patria.Depth Patria.Rolls PCAC.Oren QCD.Grass.Ward Plans.Stamp.Stair
open Next.Free QCD.Entr QCD.Entr.Meridian
variable (X:Sheet c)(o:Site c)(t:Axis)(T:TaperHol)
local notation "V"=> (0:Multi 10)
local notation "D"=> punct (0:Site c)
open QCD.Entr.Goals Patria.Gall.Seals
open QCD.Globe Kit
-- fixed row.We.K. Peak norms
local notation "O"=> (0:Site c)
lemma vestF (Q:Site c→Bundle)(e: Equiv.Perm (Site c))(he:∀ i,separation i (e i)≤1)(h:∀ i, ‖Q i‖≤1): QCD.Globe.Beam (rides e Q) 1 2:=by
       have hp (e: Equiv.Perm (Site c))(hS:∀ i,separation i (e i)≤1)(Q:Site c→Bundle)(hh:∀ i, ‖Q i‖≤1): Cent id (id (α:=Site c)) 1 2 (rides e Q):=by
           intro i; unfold Gan; simp only[id]; rw[sum_eq_single (e i)]
           · rw [show QCD.Run.cell (rides e Q) i (e i)=Q i from (by ext; rw [QCD.Stew.board,if_pos rfl])]; apply (mul_le_mul (show costS 1 i (e i) ≤ (2:ℝ) from ?_) (hh _) (norm_nonneg _) (by norm_num)).trans; norm_num
             unfold costS; have hv:(separation i (e i):ℝ) ≤1:=by exact_mod_cast hS i
             rw [pow_one]; linarith -- adjust
           · intro j _ h; rw [show QCD.Run.cell (rides e Q) i j=0 from (by rw [QCD.Stew.board,if_neg h.symm]),norm_zero,mul_zero]
           simp
       refine ⟨hp e he Q h,?_⟩; rw [←Matrix.star_eq_conjTranspose,Lat.ride_ad]; apply hp; · intro i; rw [separation_comm, ← Equiv.apply_symm_apply e i]; simpa using he (e.symm i)
       intro i; simpa using h (e.symm i)
lemma surgeP : Beam (c:=c) (shift 0 (1:Grid c) t) 1 2∧ Beam D 1 2:=by
       constructor
       · unfold Lat.shift; refine vestF _ _ (fun i=> Work.E01.sep_step_le i t) fun i=>?_ ; exact Lat.rotation_price (touch_u (thread_u ..)) -- sig find
       unfold punct; refine vestF _ _ (fun i=>by simp) (fun i=>?_); split<;> simp
local notation "P"=> shift 0 (1:Grid c) t
local notation "w"=> step (S:=Per c) t
lemma rendered (e: Equiv.Perm (Site c))(Q:Site c→Bundle)(i j:Site c) (h:i≠ e.symm O): QCD.Run.cell (((rides e Q)*D)*X) i j=0:=by
        unfold punct; rw [ride_mul,Bay.cell_ride_left, if_neg (show e i≠ O from fun h'=> h (e.apply_eq_iff_eq_symm_apply.mp h')),mul_zero,zero_mul]
lemma presentR (e: Equiv.Perm (Site c))(Q:Site c→Bundle)(i j:Site c) (h:j≠ e O): QCD.Run.cell (X*(D * rides e Q)) i j=0:=by
        let Vx:= (X*(D*rides e Q)); apply star_injective; rw [star_zero,← QCD.Run.cell_flip]; change QCD.Run.cell (star Vx) j i=0; unfold Vx; rw [star_mul,star_mul,show star D=D from ?_,Lat.ride_ad]; exact rendered _ (e.symm) _ _ _ h -- edit
        unfold punct; rw [Lat.ride_ad]; congr 1; funext i; simp only [Equiv.refl_symm,Equiv.refl_apply]; split<;> simp
noncomputable def aBall (T:TaperHol)(t:Axis)(u v:Site c):= ballast (0: Multi 10) (leadR t) T.T u v
local notation "K"=> aBall (c:=c) T t
private lemma al1 (a b:Site c)(hp:separation O a≤1) : ‖K a b‖ ≤ costS 1 a b:=by
        unfold aBall ballast; rw [norm_mul,(veil t T a).2,(veil ..).1]; apply (mul_le_of_le_one_left (norm_nonneg _) (tintE ..)).trans; apply (N_price ..).trans; rw[costS,pow_one]; have he:pdist b=separation O b:=by rw [separation_comm, separation,sub_zero]
        rw [he]; exact_mod_cast ((separation_triangle O a b).trans (Nat.add_le_add_right hp _)) -- cast of add one.
private lemma al2 (a b:Site c)(hp:separation O b≤1) : ‖K a b‖ ≤ costS 1 b a:=by
        unfold aBall ballast; rw [norm_mul,(veil t T a).2,(veil ..).1]; apply (mul_le_of_le_one_left (norm_nonneg _) (tintE ..)).trans; apply (N_price ..).trans; have he: pdist b≤1:=by rw [separation_comm, separation,sub_zero] at hp; exact hp
        apply (show (pdist b:ℝ) ≤1 from (by exact_mod_cast he)).trans; exact cost_one ..
noncomputable def viewX(T: TaperHol)(t:Axis): Sheet c→ₗ[ℂ] Bundle:= {
       toFun:=fun M=> ∑ x:Site c,∑ v:Site c,aBall T t x v • QCD.Run.cell M x v,map_add':=fun M N=> by
           simp_rw [show ∀ x y:Site c, QCD.Run.cell (M+N) x y= QCD.Run.cell M x y+QCD.Run.cell N x y from fun _ _=>rfl,smul_add, Finset.sum_add_distrib]
       map_smul':=fun a X=>by simp_rw [QCD.Run.cell_scale, Finset.smul_sum]; exact sum_congr rfl fun x _=> sum_congr rfl fun y _=> smul_comm .. }
local notation "Y"=> viewX T t
open QCD
variable (e:Equiv.Perm (Site c))(Q:Site c→Bundle)(he:Beam (rides e Q) 1 2) (h:∀ i,separation i (e i)≤1)(hV:Beam X 1 C)
include he h hV
lemma raysK : let W:= Y (((rides e Q)* D)*X-X*(D* (rides e Q)))
         ‖W‖ ≤8*C:=by
       let G:= rides e Q; let W:= G*D; let L:= D*G; let A:=W*X; let B:=X*L
       have hp:0 ≤ C:=(norm_nonneg _).trans (Cent.bike hV.toR 0 0)
       have ht:= (surgeP (c:=c) t).2
       have hA : Beam A 1 (2*2*C):= (he.op ht (by norm_num) (by norm_num)).op hV (by norm_num) hp
       have hB: Beam B 1 (C*(2*2)):= hV.op (ht.op he (by norm_num) (by norm_num)) hp (by norm_num)
       let x:=e.symm O; let y:= e O
       have hm: ‖Y A‖ ≤ 2*2*C :=by
                 change ‖∑ u:Site c,∑ v: Site c,_‖ ≤ _; rw [sum_eq_single x]; apply le_trans _ (hA.toR x); swap
                 · intro i _ hv; simp_rw [show ∀ u: Site c,QCD.Run.cell A i u=0 from fun u=>rendered X e Q i u hv, smul_zero,sum_const_zero]
                 rotate_right; · simp
                 apply (norm_sum_le ..).trans; apply sum_le_sum; intro i _; rw[norm_smul]; apply mul_le_mul_of_nonneg_right (al1 t T x i ?_) (norm_nonneg _); rw[separation_comm]; simpa [x] using h (e.symm O)
       have hg: ‖Y B‖ ≤ C*(2*2) := by
                 change ‖∑ u:Site c,∑ v:Site c,_‖ ≤ _; rw[sum_comm, sum_eq_single y]; apply le_trans _ (hB.axR y); swap
                 · intro i _ hv; simp_rw [show ∀ u: Site c,QCD.Run.cell B u i=0 from fun u=> presentR X e Q u i hv,smul_zero,sum_const_zero]
                 rotate_right; · simp
                 apply (norm_sum_le ..).trans; apply sum_le_sum; intro i _; rw[norm_smul]; change _≤costS 1 y i * ‖QCD.Run.cell _ _ _‖; rw[QCD.Run.cell_flip,norm_star]; exact mul_le_mul_of_nonneg_right (al2 t T i y (h O)) (norm_nonneg _)
       intro Ws; change ‖Y (A-B)‖≤ _; rw [map_sub]; apply (norm_sub_le ..).trans ((add_le_add hm hg).trans (le_of_eq (by ring)))
end YM.Massive.Patria.Gall.Cahoots
#print axioms YM.Massive.Patria.Gall.Cahoots.rendered
#print axioms YM.Massive.Patria.Gall.Cahoots.surgeP

#print axioms YM.Massive.Patria.Gall.Cahoots.raysK
