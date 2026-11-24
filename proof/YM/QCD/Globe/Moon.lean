import YM.QCD.Globe.Belay
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
variable {X:Kit.Rail f c}(o:Site f)
noncomputable abbrev rainier (R:Sheet f)(B: Cover→ Alder c):Alder c:= (↑(Fintype.card Signed):ℂ)⁻¹ • ∑ v:Site f, ∑ i:Signed, (fun y:Site c=> onset R o (foam i v)* B (foam i v) y)
lemma rotatedE (R:Sheet f)(X:Kit.Rail f c): rainier o R (vial X o)=cell (R*X) o:=by
    let M(v:Site f):= (fun i:Site c=> cell R o (o+v)*cell X (o+v) i)
    have he(v:Site f)(i:Signed)(p:Site c): onset R o (foam i v)* vial X o (foam i v) p= M v p:=by unfold onset vial; rw [Pi.smul_apply,Matrix.smul_mul, Matrix.mul_smul, smul_smul,(oaub _ _).1,one_smul,foams]
    unfold rainier; funext p; rw [Pi.smul_apply,Finset.sum_apply]; simp_rw [Finset.sum_apply,he,sum_const,card_univ]; rw [← Finset.smul_sum,← Nat.cast_smul_eq_nsmul ℂ,smul_smul, inv_mul_cancel₀ (show (Fintype.card Signed:ℂ)≠0 from by exact_mod_cast Fintype.card_ne_zero (α:=Signed)),one_smul,cell_mul]; exact Equiv.sum_comp (Equiv.addLeft o) (fun v=>cell R o v*cell X v p)
lemma rotated0 (R:Sheet f)(Y W: Cover→ Alder c): rainier o R (Y-W)=rainier o R Y - rainier o R W:=by funext p; simp only [rainier, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply,Matrix.mul_sub,sum_sub_distrib,smul_sub]
lemma foams_bill (i:Signed)(p: Site f):Laurent.size (foam i p) ≤ 4*pdist p:=by
    unfold Laurent.size; refine (sum_le_sum (fun j (_ : j∈(univ:Finset Axis))=> foam_cost i p j)).trans ?_; simp [Axis]
def Drier (X:Sheet f):Prop:=∀ o D,pina o D X=0
lemma Tempo.staid {U:Sheet f}(h:Tempo U)(hp:∀ i,pina 0 i U=0): Drier U:=by
   intro p i; change Pina U p i=0; cases i
   · exact (h.night p).trans ((h.night 0).symm.trans (hp none))
   next i=> exact (h.flange p i).trans ((h.flange 0 i).symm.trans (hp (some i)))
lemma rotated1 (R:Sheet f)(B: Cover→ Alder c)(hp:Drier R) : rainier o R (fun _=> B 0)=0 ∧ rainier o R (fun v=>firstA v B)=0:=by
   constructor
   · funext i; unfold rainier; simp_rw [Pi.smul_apply, Finset.sum_apply, ← Matrix.sum_mul,← Matrix.smul_mul]; change _= (0:Bundle); refine Eq.trans ?_ (zero_mul (B 0 i)); refine congr_arg (·*(B 0 i)) ?_; have he:= hp o none; change Pina R o none=0 at he; simpa only [Pina, Option.elim_none, one_smul] using he
   funext i; unfold rainier firstA; simp only [Pi.smul_apply, Finset.sum_apply,Matrix.mul_sum,Matrix.mul_smul]; let M:= (↑(Fintype.card Signed):ℂ)⁻¹; rw [sum_wind _]; rw [Finset.smul_sum]; change _=(0:Bundle); apply sum_eq_zero; intro j _; simp_rw [← Matrix.smul_mul, ← Matrix.sum_mul, ← Matrix.smul_mul]; change Pina R o (some j)*stepA j B 0 i=0; rw [show Pina R o (some j)=0 from hp o _, zero_mul]
 where sum_wind (g: Site f→ Signed → Axis → Bundle): ∑ i:Site f, ∑ j, ∑ t,g i j t=∑ t:Axis, ∑ i:Site f, ∑ j,g i j t:=by
        simp_rw [sum_comm (s:= (univ:Finset Signed)) (t:= (univ:Finset Axis))]; rw [sum_comm]

lemma rotatedR (R:Sheet f)(X:Kit.Rail f c)(hp:Drier R):rainier o R (fun v=>remnant v (vial X o))=cell (R*X) o:=by
     let z:= vial X o
     change rainier o R (fun v=>z v-z 0-firstA v z)=_; have hv:(fun v=>z v-z 0-firstA v z)=(z-(fun _=>z 0))-(fun v=>firstA v z):=rfl; rw [hv]
     have hx:= rotated0 o R (z-(fun _=>z 0)) (fun v=>firstA v z); rw [rotated0 o R z (fun _=>z 0),(rotated1 o R z hp).1,(rotated1 o R z hp).2,sub_zero,sub_zero] at hx; exact hx.trans (rotatedE o R X)
variable {t A: ℝ}{R:Sheet f}{r: Ratio c f}
def moldH (a:ℝ)(m:ℕ)(V:Side):ℝ:= a*(3*3^m*((V.val:ℝ)⁻¹)^2)*4^m -- edit
lemma rotatedPay (hR:Drier R)(ht:2 ≤ m)(hA:0≤A)(hk: Beam R m t)(hp: tithe X r A m): Cent r.parent id m (t*moldH A m r.count) (R*X):=by
    intro o; change fir (r.parent o) m (cell (R*X) o) ≤ _; rw [←rotatedR o R X hR];
    let Z:=vial X o; let z:=moldH A m r.count; have he:0≤ z:=by unfold z moldH; positivity
    have h(j:Signed)(v:Site f): fir (r.parent o) m (remnant (foam j v) Z) ≤ z * costS m o (o+v):=by
         apply le_trans (reminisce o _ (foams_bill j v) hp ht hA); unfold z moldH costS; rw [separation]; push_cast; rw [show o-(o+v)=-v by abel,pdist_neg,mul_assoc _ (4^m:ℝ),← mul_pow]; gcongr; linarith
    unfold rainier; let K(v:Site f):= costS m o (o+v)* ‖cell R o (o+v)‖
    have hh (i:Site f)(j:Signed):‖onset R o (foam j i)‖=‖cell R o (o+i)‖:= by unfold onset;rw [norm_smul, foams,pathLength,one_mul]
    rw [fir_s]; apply le_trans (b:=‖(↑(Fintype.card Signed):ℂ)⁻¹‖*(∑ i: Site f, ∑ _ : Signed, z*K i))
    · apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); apply (fir_sum ..).trans; apply sum_le_sum; intro i _; apply (fir_sum ..).trans; apply sum_le_sum; intro j _; exact (fir_l ..).trans ((mul_le_mul_of_nonneg_left (h j i) (norm_nonneg _)).trans_eq (by unfold K; rw [hh]; ring))
    have hg : (Fintype.card Signed:ℝ)≠0:=by exact_mod_cast Fintype.card_ne_zero (α:=Signed)
    simp only [sum_const,nsmul_eq_mul, card_univ]; rw [norm_inv, show ‖(Fintype.card Signed:ℂ)‖= (Fintype.card Signed:ℝ) from ?_,← mul_sum,inv_mul_cancel_left₀ hg,← mul_sum, mul_comm t]; · apply mul_le_mul_of_nonneg_left _ he; exact (Equiv.sum_comp (Equiv.addLeft o) (fun i=> costS m o i * ‖cell R o i‖)).trans_le (hk.toR _)
    simp
end YM.QCD.Globe
