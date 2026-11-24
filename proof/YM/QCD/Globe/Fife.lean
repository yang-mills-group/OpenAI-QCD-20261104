import YM.QCD.Globe.Foils
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
variable (S h){X:Sheet c}
open Fork Nola
lemma Tempo.tone (hx: Tempo X)(x:Site c)(v:Cover): onset X x v=onset X 0 v:=by rw [hx.giltV,hx.stillG,hx.giltV]; -- order?
lemma Tempo.uniform (hx:Tempo X) (p x:Site c): Gan id id m X p= Gan id id m X x:=by
     unfold Gan; let C (a y:Site c):=costS m a y* ‖cell X a y‖; have ht (a):Gan id id m X a=∑ i,C a (a+i):=Eq.symm (Equiv.sum_comp (Equiv.addLeft a) (C a))
     change Gan id id m X p= Gan id id m X x; rw [ht,ht]; refine sum_congr rfl (fun i _=>?_)
     have hu (z:Site c) : ‖onset X z (lift i)‖=‖cell X z (z+i)‖:=by unfold onset; rw [wrap_lift,norm_smul, pathLength, one_mul]
     unfold C; rw [← hu,← hu,hx.tone,hx.tone x]; apply congr_arg (· * _); unfold costS separation; rw [show p-(p+i)=x-(x+i) by abel]
lemma centsT {u x:ℝ}(hx: Cent id id m u X)(hp: Tempo X):Beam X m u:=by
     refine ⟨hx,?_⟩; have ht: Ton id (id (α:=Site c)) m (1:ℝ) (chirality c):=?_; have hg:Xᴴ=chirality c*X*chirality c:= (Orbit.funds0 _).1 hp.song
     · rw [hg]; have hu: 0 ≤ u:=le_trans (sum_nonneg fun i _=>mul_nonneg (cost_nn ..) (norm_nonneg _)) (hx 0)
       have he:= Cent.op (Cent.op ht.toR hx hu) ht.toR zero_le_one; rw [one_mul,mul_one] at he; exact he
     have he (i j:Site c) : cell (chirality c) i j= if i=j then wave g5 else 0:=by
          ext a b; rw [cell]; split
          next h=> rw [← h]; simp [Matrix.of_apply, chirality,onSpin,Lat.rides]
          next h=> simp [Matrix.of_apply, chirality,onSpin,Lat.rides,h]
     have hp': ‖wave g5‖ ≤ 1:=Lat.rotation_price (wobble _ ⟨by simp,by simp⟩)
     have hv: Cent id id m (1:ℝ) (chirality c):=fun v=>by
           unfold Gan; rw [sum_eq_single v]; · simpa [he, costS] using hp'
           · intro i _ h; simp [he,h.symm]
           simp
     exact ⟨hv,Eq.subst (motive:=fun x=>Cent id id m (1:ℝ) x) chi_star.symm hv⟩
lemma tone_bill {a:ℝ}(hx: Cent id id m a X)(hp:Tempo X)(he:1 ≤ m):|mass X|≤ a ∧ |sheen X| ≤ a :=by
    have hf (u:Option Axis): ‖Pina X 0 u‖≤ a:=by
         unfold Pina; let r:ℂ:=↑(Fintype.card Signed); have hr:r≠0:=by unfold r; exact_mod_cast Fintype.card_ne_zero (α:=Signed)
         let g(j:Site c):=costS m 0 j * ‖cell X 0 j‖
         let d (j:Site c)(i:Signed):Bundle:= (u.elim (1:ℂ) fun a=> ↑(foam i j a)) • onset X 0 (foam i j)
         have hD (j i): ‖d j i‖≤ g j:=by
             unfold d g onset; rw [norm_smul, norm_smul, pathLength,foams,zero_add,one_mul]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); cases u
             · rw [Option.elim_none,norm_one]; apply cost_one
             next a=>
                rw [Option.elim_some, show ‖(↑(foam i j a):ℂ)‖=(↑(foam i j a).natAbs:ℝ) by simp]
                unfold costS; rw [separation_comm 0,separation, sub_zero]; refine le_trans (Nat.cast_le.mpr (foam_cost ..)) ((le_add_of_nonneg_left zero_le_one).trans (le_self_pow₀ ?_ (by omega))); simp
         change ‖r⁻¹ • ∑ j,∑ i,d j i‖ ≤ _; rw [norm_smul]; apply le_trans (b:=‖r⁻¹‖*∑ j,∑ _ : Signed, g j)
         · apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); exact (norm_sum_le ..).trans (sum_le_sum fun i _=> (norm_sum_le ..).trans (sum_le_sum fun j _=> hD ..))
         simp only [sum_const,nsmul_eq_mul]; rw [← mul_sum,norm_inv]; change _≤ a; have hh:‖r‖=↑(Fintype.card Signed):=by simp[r]
         rw [card_univ,← mul_assoc,← hh,inv_mul_cancel₀ (norm_ne_zero_iff.mpr hr),one_mul]; exact hx 0
    exact ⟨(lesson _).trans_le ((congr_arg (‖·‖) (hp.night 0)).symm.trans_le (hf none)) ,(lesson_s (0:Axis) (sheen X)).trans_le ((congr_arg (‖·‖) (hp.flange 0 0)).symm.trans_le (hf (some 0)))⟩
end YM.QCD.Globe
