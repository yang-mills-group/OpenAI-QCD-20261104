import YM.QCD.Entr.Galley
import YM.QCD.Pearl.Steer
/-! # sound coefficient calibration no exact torus derivative assumptions from T.Images. Estimate from path signature. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Entr
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z:ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Eyrie Rudder Sparks Pearl YM.Next.Free Bloch Laurent
variable {Γ:Silo c}{A: BankP c}{U:St c}
noncomputable def pen (G:Gleam):Spike:= (↑(stop (0:Cover) G.w 0):ℂ) • G.B
lemma glasses (G:Gleam) (x:Site c): flange (G.dept 0 1) x=(Stew.shine x (stop x G.w)*(crest (stop x G.w-x):ℂ)) • (shimmer 0 x G.w • G.B):=by
    have he(a:Site c): Run.cell (G.dept 0 1) x a= if stop x G.w=a then shimmer 0 x G.w • wave G.B else 0:=by
        unfold Gleam.dept onSpin; rw [pinned, ride_mul,board,Equiv.trans_refl]; rw [show Equiv.addRight _ x=stop x G.w from (wrap_stop ..).symm, Sparks.rack, Matrix.smul_mul,one_mul]
    unfold flange; simp_rw [he]; rw [sum_eq_single (stop x G.w)]; · rw [if_pos rfl]; congr 1; exact (gold_s ..).trans (congr_arg _ (leafy _))
    · intro j _ hz; rw [if_neg hz.symm,gold0,smul_zero]
    simp
lemma grand (x:Cover) (i:Axis): Int.natAbs (x i) ≤ Laurent.size x:=single_le_sum (fun i _=> Nat.zero_le (Int.natAbs (x i))) (mem_univ i)
lemma stopBud (X:Walk): Laurent.size (stop (0:Cover) X)≤ X.length:=by simpa [Laurent.size] using stepStop (0:Cover) X
lemma grape (G:Gleam)(x:Site c)(h:2*G.w.length< c.val): flange (G.dept (0:Site c) 1) x=pen G:=by
    let Y:=stop (0:Cover) G.w; let i:=stop x G.w; have hx: lift (i-x)=Y:=by
        apply lift_eq_iff.mpr; refine ⟨by unfold i; rw [wrap_stop]; unfold Y; abel,fun i=>?_⟩; have ht: (Y i).natAbs ≤ G.w.length:= (grand Y i).trans (stopBud _); omega
    rw [glasses,show Stew.shine x i=shimmer 0 x G.w from Stew.shore _ _ _ hx.symm,smul_smul,mul_right_comm]; unfold pen crest; rw [hx]; obtain h|h:=glisten (0:Site c) x G.w <;> rw [h] <;> simp [Y]
lemma gulf (G:Gleam)(x:Site c): ‖flange (G.dept (0:Site c) 1) x‖≤ G.w.length * ‖G.B‖ :=by
    let i:=stop x G.w; have hx:=Eyrie.stopped G.w x; rw [separation_comm] at hx
    have hh : |crest (i-x)| ≤ (G.w.length:ℤ):=by rw [← Int.natCast_natAbs]; exact_mod_cast ((component_le (i-x) 0).trans hx) -- type
    have hp:‖shimmer (0:Site c) x G.w‖=1:=by obtain h|h:=glisten (0:Site c) x G.w <;> simp [h]
    have hs:‖Stew.shine x i‖=1:=by obtain h|h:=Stew.shines x i <;> simp [h]
    rw [glasses,norm_smul,norm_mul,hs,one_mul,norm_smul,hp,one_mul,Complex.norm_intCast]; refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _); exact_mod_cast hh
lemma peg_cash (G:Gleam): ‖pen G‖≤G.w.length * ‖G.B‖:=by
    have hp: |stop (0:Cover) G.w 0| ≤ (G.w.length:ℤ):=by rw [← Int.natCast_natAbs]; exact_mod_cast ((grand _ 0).trans (stopBud _))
    unfold pen; rw [norm_smul,Complex.norm_intCast]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); exact_mod_cast hp
lemma longBill (G:Gleam)(x : Site c): c.val * ‖flange (G.dept (0:Site c) 1) x-pen G‖ ≤ 4*G.w.length^2 * ‖G.B‖ :=by
   by_cases h:2*G.w.length < c.val; · rw [grape G x h,sub_self,norm_zero,mul_zero]; positivity
   push_neg at h
   exact ((mul_le_mul (show (c.val:ℝ) ≤ 2*(G.w.length:ℝ) from by exact_mod_cast h) ((norm_sub_le ..).trans (add_le_add (gulf ..) (peg_cash G))) (norm_nonneg _) (by positivity)).trans_eq (by ring)) -- cast Nat power check
lemma grants (ha:0<η)(G:Gleam)(n:Side): n.val*‖torque n (G.dept 0 1) - (Fintype.card (Site n)) • pen G‖ ≤ (4*(Fintype.card (Site n):ℝ)*Reserves.polyPrice η 2) * G.rate η :=by
   change _*‖(∑ x,flange (G.dept 0 1) (x:Site n))-_‖ ≤ _; rw [show Fintype.card (Site n) • pen G=∑ x:Site n,pen G from (by rw [sum_const,card_univ]), ← sum_sub_distrib]; apply (mul_le_mul_of_nonneg_left (norm_sum_le ..) (Nat.cast_nonneg _)).trans; rw [mul_sum]; apply (sum_le_sum fun i _=> longBill G i).trans
   rw [sum_const,card_univ,nsmul_eq_mul]; let b:ℝ:= G.w.length; have hh : b^2 ≤ Reserves.polyPrice η 2 * Real.exp (η*b):=(pow_le_pow_left₀ (Nat.cast_nonneg _) (le_add_of_nonneg_left zero_le_one) 2).trans (polynomial_cost ha (Nat.cast_nonneg _) 2) -- tag
   unfold Gleam.rate; rw [mul_assoc]; apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hh (norm_nonneg _)) (by norm_num : (0:ℝ) ≤4)) (Nat.cast_nonneg (Fintype.card (Site n)))).trans_eq; unfold b; ring
lemma blooms_dummy (i:ℕ)(h:0≤η): Fractal (PEmpty.elim: PEmpty.{1}→ Bloom i) η 0 :=⟨h,fun i=>i.elim,Summable.of_finite,by rw [tsum_empty]⟩ -- implicit
variable {ι:Type} {G:ι→Gleam}{Q:Plan j} {V:Train j}
lemma plants (x:Gleam): (-Complex.I) • goldL (Pearl.dew (step 0) (boom x) 0)=pen x:=by
    rw [Pearl.progFirst, Pearl.gle, boom,show wane (0:Momentum) x.w=1 from ?_,one_mul,map_smul,show goldL (wave x.B)=x.B from leafy _,smul_smul]; unfold pen; rw [← mul_assoc,neg_mul,Complex.I_mul_I,neg_neg,one_mul] -- sign
    unfold Pearl.wane; simp [mode] -- route def
lemma venture (he:0<η)(H:Rudder.Wages (4*η) a G)(hp:Rudder.Shows G (fun n t=> Pine.wood Q t V)): HasSum (pen ∘ G) (Lat.gamma 0):=by
    have h:=show Pearl.Package η a 0 0 Q V G _ _ from ⟨he,H,hp,blooms_dummy 1 (by positivity), blooms_dummy 2 (by positivity)⟩
    have he:= (prog_demand h (step 0)).2; rw [halis h] at he; have hz:= (goldL.hasSum he).const_smul (-Complex.I); rw [map_smul,show goldL (wave (Lat.gamma 0))=Lat.gamma 0 from leafy _, smul_smul,neg_mul,Complex.I_mul_I,neg_neg,one_smul] at hz; exact hz.congr_fun fun i=> (plants _).symm
lemma wagesV (he:0<η)(H:Rudder.Wages (4*η) a G)(hp:Rudder.Shows G (fun n t=> Pine.wood Q t V))(n:Side): n.val*‖torque n (Pine.wood Q 0 V 1)- Fintype.card (Site n) • Lat.gamma 0‖ ≤ (4*(Fintype.card (Site n):ℝ)*Reserves.polyPrice (4*η) 2)* a:=by
    let C:ℕ:= Fintype.card (Site n); have h:= ((torque n).hasSum (hp n 0 1)).sub ((venture he H hp).const_smul C)
    let g i:=torque n ((G i).dept 0 1)-C • pen (G i); have hx:= (h.tsum_eq); rw [←hx]; change (n.val:ℝ)*‖∑' i,g i‖≤ _
    have ht : Summable fun i=> ‖g i‖:= Summable.norm h.summable
    apply (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm ht) (Nat.cast_nonneg _)).trans; rw [← tsum_mul_left]; let P:ℝ:= 4*C*Reserves.polyPrice (4*η) 2
    apply ((ht.mul_left (n.val:ℝ)).tsum_le_tsum (fun i=> grants (show 0<4*η by positivity) (G i) n) (H.val.mul_left _)).trans; rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left H.cap (by unfold Reserves.polyPrice; positivity)
end YM.QCD.Entr
