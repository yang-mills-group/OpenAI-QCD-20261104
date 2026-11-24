import YM.DawnS.Jerry
import YM.Next.MAXWELL.Strict
/-! Triviality of spatial polynomial killing every projected ray. -/
set_option autoImplicit false
noncomputable section
namespace YM.DawnS
open Function Set Filter Finset Lattice Analysis MeasureTheory Tensor TensorProduct Maxwell Arise.Range Massive Massive.UV Massive.UV.Free QCD QCD.Lat Grass
open scoped Topology ContDiff BigOperators InnerProductSpace TensorProduct Classical Matrix
local notation "K"=> timeAxis
local notation "I₀"=>Complex.I
local notation "P"=> RingS
local notation "Y"=>Vertex
local notation "Ω"=>muS
variable {d:ℕ}
noncomputable def reverse(z:P):P:=⟨-z.val,by rw[mem_sphere_zero_iff_norm,norm_neg,flash]⟩
local notation "ZR"=>YM.DawnS.reverse
lemma invertG (z:PR)(i:chit d)(v:Bool)(r:ℝ): gleam v i r (-z.1, ZR z.2)=gleam v i r z:=by rw [scoreG,scoreG]; simp only[neg_div, reverse,neg_smul,smul_neg,neg_neg]
lemma whale (z:P)(v:Bool): lampS v z+lampS v (ZR z)=(2:ℂ) • (1:Spike):=by
     let g:= I₀ • (gamma K* spark z); have he : I₀ • (gamma K*spark (ZR z)) = -g:=by rw[show spark (ZR z)=-spark z from colS z,mul_neg,smul_neg];
     cases v
     · rw [stamp z,stamp (ZR z),he]; change (1+g).transpose +(1+ -g).transpose= _; rw [←Matrix.transpose_add,show ((1:Spike)+g)+(1+ -g)=1+1 by abel];simp [two_smul]
     rw [stamp z,stamp (ZR z),he]; change ((1:Spike)+g)+(1+ -g)=_; rw [two_smul]; abel
noncomputable def bandIT (c:Peak d→ℂ)(x:PR)(r:ℝ)(v:Bool)(i:Pinor):ℂ:=∑ j,c j*shot v j i r x
variable (c:Peak d→ℂ)(r:ℝ)(hr:0<r)(v:Bool)
lemma hazed(i:Pinor): Continuous fun x=>bandIT c x r v i:=continuous_finsetSum _ fun q _=>continuous_const.mul (continuousShot ..)
lemma analyticG(z:P)(a:ℝ)(i:Pinor): AnalyticAt ℝ (fun t:ℝ=>bandIT c (t,z) r v i) a:=by
       apply ContDiffAt.analyticAt; refine ContDiffAt.sum fun i _=>?_ ; unfold shot gleam; dsimp only; exact contDiffAt_const.mul (contDiffAt_const.mul (((show ContDiffAt ℝ ω (fun t:ℝ=> (↑(t/r):ℂ)) a from Complex.ofRealCLM.contDiff.contDiffAt.comp _ (contDiffAt_id.div_const r)).pow _).mul contDiffAt_const))
include hr
lemma peakGone(h:∀ z:PR,z.1>0→∀ i,bandIT c z r v i=0): c=0:=by
       have hp(x:PR)(i:Pinor): bandIT c x r v i=0:=by
             obtain ⟨t,z⟩:=x; have hE : AnalyticOnNhd ℝ (fun t:ℝ=>bandIT c (t,z) r v i) Set.univ:= fun t _=> analyticG c r v z t i
             exact hE.eqOn_zero_of_preconnected_of_eventuallyEq_zero (z₀:=(1:ℝ)) isPreconnected_univ (Set.mem_univ _) (by filter_upwards [isOpen_Ioi.mem_nhds (show (1:ℝ)∈Set.Ioi 0 from (by simp))] with t ht; exact h (t,z) ht i) (Set.mem_univ t)
       ext1 x; obtain ⟨p,a⟩:=x; refine declares v r hr (fun i:chit d=>c (i,a)) (fun x=> ?_) p
       have he :bandIT c x r v a+bandIT c (-x.1,ZR x.2) r v a=0:=by rw [hp,hp,add_zero]
       unfold bandIT at he; rw[← sum_add_distrib] at he; let g (i:Peak d) :ℂ:=gleam v i.1 r x
       have hf(i:Peak d): shot v i a r x+shot v i a r (-x.1,ZR x.2)=2*(1:Spike) a i.2*g i:=by
             unfold shot; rw [invertG, ← add_mul, show lampS v x.2 a i.2 + lampS v (ZR x.2) a i.2= _ from congr_fun (congr_fun (whale x.2 v) a) i.2]; rfl -- maybe after metav dep
       simp_rw[← mul_add,hf] at he; rw[Fintype.sum_prod_type] at he; -- order (chit→pinor)
       let f(i:chit d):= c (i,a)*g (i,a); apply mul_left_cancel₀ (a:=(2:ℂ)) (by norm_num); rw[mul_zero]; refine Eq.trans ?_ he; rw[Finset.mul_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [Finset.sum_eq_single a]; change _=c (i,a)*(2*(1:Spike) a a*g (i,a)); rw [Matrix.one_apply_eq,mul_one]; change 2*_=_*(2*gleam v i r x); ring
       intro j _ ht; simp [Matrix.one_apply, ht.symm]
       simp
end YM.DawnS
#print axioms YM.DawnS.peakGone
