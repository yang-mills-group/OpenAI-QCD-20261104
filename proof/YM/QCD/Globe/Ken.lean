import YM.QCD.Globe.Days
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
open Laurent Bloch QCD.Free
variable {K: Sheet c}{A η d t:ℝ}
noncomputable def pitchP (K:Sheet c)(p:Momentum): Bundle:=(Fintype.card Signed:ℂ)⁻¹ • ∑ v:Site c, ∑ g:Signed, mode p (foam g v) • onset K 0 (foam g v)
lemma commuted (hp:Tempo K)(p i:Site c): ∑ z:Site c,scarf p z • (Run.cell K i z)=scarf p i • pitchP K (tuning p):=by
     let A:= Fintype.card Signed; have hA:(A:ℂ) ≠0:=by unfold A; exact_mod_cast Fintype.card_ne_zero (α:=Signed)
     unfold pitchP; rw [smul_comm, Finset.smul_sum]; have he x g : scarf p i • (mode (tuning p) (foam g x) • onset K 0 (foam g x))=scarf p (i+x) • Run.cell K i (i+x):=by
         rw [← hp.tone i, smul_smul, ← concord, onset,smul_smul, foams, mul_right_comm, (oaub (foam g x) i).1,one_mul]
     simp_rw [Finset.smul_sum,he,sum_const,card_univ]; rw [← Equiv.sum_comp (Equiv.addLeft i) (fun z:Site c=>scarf p z • Run.cell K i z),← Finset.smul_sum, ← Nat.cast_smul_eq_nsmul ℂ, ←Finset.smul_sum,smul_smul,mul_inv_cancel₀ hA,one_smul]; rfl
lemma imageP (hp:Tempo K):peel K=lined (pitchP K∘tuning):=by
     apply peel_eq; ext ⟨p,i⟩ ⟨x,j⟩; have he:Run.cell (K*leaf c) p x=scarf x p • pitchP K (tuning x):=by
         rw [Run.cell_mul,← commuted hp x p]; apply sum_congr rfl; intro z _; rw [show Run.cell (leaf c) z x=scarf x z • 1 from rfl, Matrix.mul_smul,Matrix.mul_one]
     rw [Free.face]; exact congr_fun (congr_fun he i) j -- defeq
-- norm remainder. moment lengthSq.
def tension (p: Momentum)(x:Cover):ℂ:=Complex.I*∑ i, p i*x i
lemma shake (x:ℂ)(h:‖Complex.exp x‖=1): ‖Complex.exp x-1-x‖ ≤ 4*‖x‖^2:=by
    rcases le_total ‖x‖ 1 with h|he; · exact (Complex.norm_exp_sub_one_sub_id_le h).trans (le_mul_of_one_le_left (sq_nonneg _) (by norm_num))
    apply (norm_sub_le ..).trans ((add_le_add_left (norm_sub_le ..) ‖x‖).trans _); rw [h,norm_one]; nlinarith
lemma earnest (p:Momentum)(v:Site c)(s:Signed): ‖tension p (foam s v)‖^2 ≤ 4*lengthSq p*(pdist v)^2:=by
     let x:=foam s v
     have hG : ∑ i:Axis,‖p i*x i‖≤ ∑ i:Axis, ‖p i‖*(pdist v:ℝ):=by
          apply sum_le_sum; intro i _; rw [norm_mul,show ‖(↑(x i):ℂ)‖=((x i).natAbs:ℝ) by simp]; exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (foam_cost ..)) (norm_nonneg _)
     unfold tension; rw [norm_mul,Complex.norm_I,one_mul]; apply (pow_le_pow_left₀ (norm_nonneg _) ((norm_sum_le ..).trans hG) 2).trans; rw [← Finset.sum_mul, mul_pow]; apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
     have he:= Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (s:= (univ:Finset Axis)) (f:=fun i=> (1:ℝ)) (g:=fun i=> ‖p i‖^2) (r:=fun i=>‖p i‖) -- edit
     simpa [lengthSq] using he
lemma dry_wave (hp:Drier K)(hK:Beam K 6 A)(p:Momentum)(ht:p ∈ baseCube): ‖pitchP K p‖ ≤ 16 * lengthSq p * A:=by
    let g(s:Cover) := onset K 0 s
    let H (P: Cover→ℂ):= (Fintype.card Signed:ℂ)⁻¹ • ∑ x:Site c,∑ i:Signed,P (foam i x) • g (foam i x)
    have h0: H (fun _=>1)=0:= hp 0 none
    have h1:H (tension p)=0:=by
         let F(x:Cover)(i:Axis):=Complex.I*p i*(x i:ℂ);
         have ht(v:Cover): tension p v=∑ i,F v i:=by unfold tension F; rw [Finset.mul_sum]; simp only [mul_assoc]
         have he(i:Axis): H (fun x=> F x i)=0:=by
              have HH(k:ℂ): ∑ x:Site c,∑ s:Signed,(k*(foam s x i:ℂ)) • g (foam s x)= k • ∑ x:Site c,∑ s:Signed,(foam s x i:ℂ) • g (foam s x):=by simp_rw [Finset.smul_sum,mul_smul]
              have hv:=hp 0 (some i); change H (fun v=>(v i:ℂ))=0 at hv; unfold H F; rw [HH (Complex.I*p i),smul_comm]; rw [show (Fintype.card Signed:ℂ)⁻¹ • ∑ x:Site c,∑ s:Signed,(foam s x i:ℂ) • g (foam s x) = 0 from hv]; simp

         unfold H; simp_rw [ht,sum_smul]; rw [-- exchange
           sum_h _]; rw [Finset.smul_sum]; exact sum_eq_zero (fun i _=>he i)
    let M(x:Cover):=mode p x-1-tension p x
    have he : pitchP K p=H M:=by
        change H _ = _; have hh : H M= H (mode p)-H (fun _=>1)-H (tension p):=by unfold H M; simp only [sub_smul,sum_sub_distrib, smul_sub];
        rw [hh,h0,h1,sub_zero,sub_zero]
    have hC: 0 ≤ lengthSq p:=sum_nonneg fun i _=>sq_nonneg _
    rw [he];
    have hB(v:Site c)(i:Signed):‖M (foam i v) • g (foam i v)‖ ≤ 16*lengthSq p*(costS 6 (0:Site c) v * ‖Run.cell K 0 v‖):=by
         let x:=tension p (foam i v); have hh:‖M (foam i v)‖≤4* ‖x‖^2:=shake _ (mode_real _ _ ht.1)
         rw [norm_smul]; unfold g onset; rw [norm_smul,foams,zero_add,pathLength,one_mul,← mul_assoc (16*lengthSq p)]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); apply hh.trans ((mul_le_mul_of_nonneg_left (earnest ..) (by norm_num : (0:ℝ) ≤4)).trans _); rw [show costS 6 0 v=(1+pdist v:ℝ)^6 from ?_];
         · have he : (pdist v:ℝ)^2 ≤ (1+pdist v:ℝ)^6:= (pow_le_pow_left₀ (Nat.cast_nonneg _) (le_add_of_nonneg_left zero_le_one) 2).trans (pow_le_pow_right₀ (by simp) (by decide)); nlinarith only [mul_le_mul_of_nonneg_left he hC]
         unfold costS separation; rw [zero_sub,pdist_neg]
    unfold H; rw [norm_smul]; apply le_trans (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (sum_le_sum (fun i _=> (norm_sum_le ..).trans (sum_le_sum fun j _=> hB i j)))) (norm_nonneg _))
    simp only [sum_const,card_univ,nsmul_eq_mul, ← mul_sum,norm_inv, show ‖(Fintype.card Signed:ℂ)‖=(Fintype.card Signed:ℝ) from (by simp)]; rw [inv_mul_cancel_left₀ (by positivity : (↑(Fintype.card Signed):ℝ) ≠0)]; exact mul_le_mul_of_nonneg_left (hK.toR _) (by positivity)
 where sum_h (F: Site c→ Signed→ Axis→ Bundle):∑ i,∑ j,∑ k,F i j k=∑ k,∑ i,∑ j,F i j k:=by simp_rw [sum_comm (s:= (univ:Finset Signed)) (t:= (univ:Finset Axis))]; rw [sum_comm]
end YM.QCD.Globe
