import YM.QCD.Globe.Mesa
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
open Fork Nola
variable {D E F:Type*}[Fintype D][Fintype E][Fintype F][DecidableEq D][DecidableEq E][DecidableEq F]{u:D→Site c}{v:E→Site c}{g:F→Site c}{a b t:ℝ}{X Y:ArrayL D E}{B:ArrayL E F}
def costS (n:ℕ)(x y:Site c):ℝ:= (1+(separation x y:ℝ))^n
lemma cost_nn (x y: Site c):0 ≤ costS m x y:=by unfold costS; positivity
lemma cost_one (x y:Site c):1 ≤ costS m x y:=by unfold costS; apply one_le_pow₀; simp
lemma cost_symm (x y:Site c):costS m x y=costS m y x:=by unfold costS; rw [separation_comm]
lemma cost_b (x y z:Site c):costS m x z ≤ costS m x y*costS m y z:=by
    unfold costS; rw [← mul_pow]; apply pow_le_pow_left₀ (by positivity); have he:(separation x z:ℝ) ≤ separation x y + separation y z:=by exact_mod_cast separation_triangle x y z
    nlinarith [Nat.cast_nonneg (α:=ℝ) (separation x y),Nat.cast_nonneg (α:=ℝ) (separation y z)] -- exponents
-- W6 row calculus
noncomputable def Gan (u:D→ Site c)(v:E→ Site c)(n:ℕ)(X:ArrayL D E)(i:D):ℝ:=∑ j,costS n (u i) (v j)* ‖cell X i j‖
noncomputable abbrev Cent (u:D→ Site c)(v:E→Site c)(n:ℕ)(A:ℝ)(X:ArrayL D E):Prop:=∀ i,Gan u v n X i≤ A
structure Ton (u:D→ Site c)(v:E→ Site c)(m:ℕ)(A:ℝ) (X:ArrayL D E):Prop where
   toR:Cent u v m A X
   axR:Cent v u m A Xᴴ
local notation "iD" => id (α:=Site c)
noncomputable abbrev Beam (X:Sheet c)(m:ℕ)(A:ℝ):Prop:= Ton iD iD m A X -- name conflict
lemma Ton.inP (hp:Ton u v m a X):Ton v u m a Xᴴ:=⟨hp.axR,by rw [Matrix.conjTranspose_conjTranspose]; exact hp.toR⟩
lemma Cent.up (h: Cent u v m a X)(hp:a≤b): Cent u v m b X:=fun i=> (h i).trans hp
lemma Ton.up (h: Ton u v m a X)(hp:a ≤ b): Ton u v m b X:= ⟨Cent.up h.toR hp, Cent.up h.axR hp⟩
lemma Cent.op (h:Cent u v m a X)(hp:Cent v g m b B)(hb:0 ≤ b): Cent u g m (a*b) (X*B):=by
    intro i; apply le_trans _ (mul_le_mul_of_nonneg_right (h i) hb); unfold Gan; rw [sum_mul] -- a not inside
    let S j k:= costS m (u i) (v k) *‖cell X i k‖*(costS m (v k) (g j)*‖cell B k j‖)
    refine le_trans (b:=∑ j,∑ k,S j k) (sum_le_sum fun j _=> ?_) ?_
    · rw [cell_mul]; apply le_trans (b:= costS m (u i) (g j)*∑ k, ‖cell X i k*cell B k j‖) (mul_le_mul_of_nonneg_left (norm_sum_le ..) (cost_nn ..)); rw [mul_sum]; apply sum_le_sum; intro k _; exact (mul_le_mul (cost_b (m:=m) (u i) (v k) (g j)) (norm_mul_le ..) (norm_nonneg _) (mul_nonneg (cost_nn ..) (cost_nn ..))).trans_eq (by unfold S; ring)
    rw [sum_comm]; apply sum_le_sum; intro k _; unfold S; rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (hp k) (mul_nonneg (cost_nn ..) (norm_nonneg _))
lemma Ton.op (h: Ton u v m a X)(hp: Ton v g m b B)(ha:0≤a)(hb:0≤b): Ton u g m (a*b) (X*B):=⟨Cent.op h.toR hp.toR hb,by rw [Matrix.conjTranspose_mul,mul_comm]; exact Cent.op hp.axR h.axR ha⟩
lemma Gan.sub (X Y:ArrayL D E)(i:D): Gan u v m (X-Y) i ≤ Gan u v m X i+Gan u v m Y i:=by unfold Gan; rw [← sum_add_distrib]; apply sum_le_sum; intro j _; rw [← mul_add]; exact mul_le_mul_of_nonneg_left (norm_sub_le (cell X i j) (cell Y i j)) (cost_nn ..)
lemma Cent.sub (h:Cent u v m a X)(hp: Cent u v m b Y): Cent u v m (a+b) (X-Y):=fun i=> (Gan.sub ..).trans (add_le_add (h i) (hp i))
lemma Ton.sub (h:Ton u v m a X)(hp:Ton u v m b Y): Ton u v m (a+b) (X-Y):=⟨Cent.sub h.toR hp.toR,by rw [Matrix.conjTranspose_sub]; exact Cent.sub h.axR hp.axR⟩
lemma Gan.smul (X:ArrayL D E)(v':ℂ)(i:D): Gan u v m (v' • X) i= ‖v'‖ * Gan u v m X i:=by unfold Gan; rw [mul_sum]; apply sum_congr rfl; intro j _; rw [cell_scale,norm_smul,mul_left_comm]
lemma Cent.smul (h: Cent u v m a X)(v':ℂ) : Cent u v m (‖v'‖*a) (v' • X):=fun i=> (Gan.smul X v' i).trans_le (mul_le_mul_of_nonneg_left (h i) (norm_nonneg _))
lemma Ton.smul (h:Ton u v m a X)(v':ℂ): Ton u v m (‖v'‖ *a) (v' • X):=⟨Cent.smul h.toR _,by rw [Matrix.conjTranspose_smul]; exact TonSub -- edit
                                                                                                                          ⟩
 where TonSub : Cent v u m (‖v'‖ *a) (star v' • Xᴴ):=by have ht:=Cent.smul h.axR (star v'); rwa [norm_star] at ht
lemma Ton.neg (h: Ton u v m a X): Ton u v m a (-X):=by have ht := h.smul (-1); rwa [neg_one_smul,norm_neg,norm_one, one_mul] at ht
lemma Ton.add (h:Ton u v m a X)(hp:Ton u v m b Y): Ton u v m (a+b) (X+Y):=by rw [← sub_neg_eq_add X Y]; exact h.sub hp.neg
lemma Ton.one : Ton u u m 1 (1:ArrayL D D):=by
   have hh : Cent u u m 1 (1:ArrayL D D):=by
         intro i; unfold Gan; rw [sum_eq_single i]; · rw [cell_one,if_pos rfl,costS,separation_self]; simp
         · intro j _ hj; rw [cell_one,if_neg hj.symm]; simp
         simp
   exact ⟨hh,by rw [Matrix.conjTranspose_one]; exact hh⟩
lemma Gan.cont (u:D→Site c)(v:E→Site c)(m:ℕ)(i:D):Continuous fun (X:ArrayL D E)=> Gan u v m X i:=continuous_finsetSum _ fun j _=>(Run.cellC i j).continuous.norm.const_mul _ -- namespace
lemma Cent.limit {ι:Type*}(Z:ι→ ArrayL D E)(s:Filter ι)[s.NeBot](hz:Tendsto Z s (𝓝 X))(h:∀ i, Cent u v m a (Z i)): Cent u v m a X:=fun i=> le_of_tendsto ((Gan.cont u v m i).continuousAt.tendsto.comp hz) (Eventually.of_forall fun j=> h j i)
lemma Ton.limit {ι:Type*}(Z:ι→ ArrayL D E)(s:Filter ι)[s.NeBot](hz:Tendsto Z s (𝓝 X))(h:∀ i, Ton u v m a (Z i)): Ton u v m a X:=⟨Cent.limit Z s hz (fun i=>(h i).toR), Cent.limit _ s ((show Continuous fun (x:ArrayL D E)=> xᴴ from by fun_prop).continuousAt.tendsto.comp hz) (fun i=>(h i).axR)⟩
end YM.QCD.Globe
