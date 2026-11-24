import YM.QCD.Oasis.Tint
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Oasis
open Function Filter Set Metric MeasureTheory Lattice Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented
open PhysicalNext.Repeat Lapis Sienna Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare Tidings Token Shield Beam
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {E F : Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
variable {x y v b w u a U D p C s t r:ℝ}{j k c:ℕ}{i:E}{φ:E → F}
open Cove Golden NormedSpace
-- orbit navigation. Λ aux persistent.
variable {ι:Type}[Fintype ι][DecidableEq ι][FiniteDimensional ℝ E]
local notation "P'"=>ℝ×E
local notation "R"=>Poll.Body ι
variable {ρ:E→Poll.Body ι}{z : Poll.Body ι}
variable {δ: Side}{N:ℕ}{τ:E×Poll.Body ι→ EvenA δ N}
variable {Z:E× Poll.Body ι→L[ℝ] EvenA δ N}
local notation "M"=> spanV D p
open Lantern
variable (h:∀ x, ‖x‖<U → Brush k p 1 ρ x)(hu:0<U)(hs: U≤1)(hp:ρ 0=0)(hj:1≤k)
    (hL:∀ i:E×Poll.Body ι,‖i‖<1→ Brush k (w*((spanV D p)*U)^2) 1 (fun i=> τ (((spanV D p)*U) • i)-τ 0-Z (((spanV D p)*U) • i)) i) (ht:‖Z‖ ≤v)
include h hu hs hp hj hL ht
lemma norm_m (he:‖z‖ ≤ D): ‖Z (0,z)‖≤ v*D:=by
   have hx: ‖((0:E),z)‖=‖z‖:=by simp
   exact (Z.le_opNorm _).trans (mul_le_mul ht (hx.trans_le he) (norm_nonneg _) ((norm_nonneg _).trans ht))
def growT (j:ℕ)(p D w v:ℝ): ℝ:= medium j 1 p D w+v*D+1
def dawnT (j:ℕ)(p D w v:ℝ):ℝ:=growT j p D w v^2*runK j+medium j 1 p D w
lemma toldR (he:‖z‖≤ D)(x:P')(hx:‖x‖ < 1): 0 < U * growT k p D w v ∧ Brush k (U * growT k p D w v) 1 (fun i=> lyric τ ρ z (U • i)) x :=by
   let G:=medium k U p D w; have he' := moneyL (k:=k) (fun i:Poll.Body ι=> Z (0,i)) z (norm_m h hu hs hp hj hL ht he) hu.le x hx.le
   have hf:= hymnR h hu hs hp he hj x hx hL
   have hh: U^2* G+U*(v*D) < U*growT k p D w v := by
      change _ < U*(G+v*D+1); have hQ:0≤ G:= nonneg_of_mul_nonneg_right hf.nonneg (pow_pos hu _)
      nlinarith only [hu, mul_le_mul_of_nonneg_right (mul_le_of_le_one_left hu.le hs) hQ]
   exact ⟨lt_of_le_of_lt (add_nonneg hf.nonneg he'.nonneg) hh, (((hf.gathering he').climb hh.le le_rfl).shimmy (Eventually.of_forall fun i=>(sub_add_cancel ..).symm))⟩
lemma cotillon (hc:∀ x, Continuous (fun y:Poll.Body ι=>τ ((x:E),y)))(hR:U*growT k p D w v≤1): Cello (fun z x=>exp (lyric τ ρ z x)-1) (fun z=> Z (0,z)) (v*D) (dawnT k p D w v) D U k :=by
    refine ⟨Z.continuous.comp (continuous_const.prodMk continuous_id),fun i=> ?_,fun i he=>norm_m h hu hs hp hj hL ht he,fun i=> ?_,fun z i=>?_,fun z i=>?_,fun i z hx he=>?_⟩
    · exact congr_arg Z (show ((0:E),-i) = -(0,i) from Prod.ext (neg_zero.symm) rfl) |>.trans (map_neg ..)
    · apply Continuous.continuousOn; apply Continuous.sub _ continuous_const
      refine exp_continuous.comp (Continuous.sub ?_ continuous_const)
      exact (hc _).comp (show Continuous (fun z:Poll.Body ι=> ρ (1 • i.2)+(1*i.1) • z) by fun_prop)
    · unfold lyric; simp [hpoint]
    · unfold lyric; simp [hpoint]
    have hf:= hymnR h hu hs hp he hj i hx hL
    obtain ⟨H,hy⟩:= toldR h hu hs hp hj hL ht he i hx
    apply (((unpays hy H hR).gathering hf).climb ?_ le_rfl).shimmy
    · exact Eventually.of_forall fun a=> by dsimp only; abel -- goal order
    unfold dawnT; apply le_of_eq; unfold medium; ring

abbrev goreR (τ:E×Poll.Body ι→EvenA δ N)(ρ:E→Poll.Body ι): E→EvenA δ N:= fun x=>τ (x,ρ x)-τ 0
abbrev keenR (j:ℕ)(p D v w U:ℝ):= let M':=spanV D p; v*(M'*U*2) + clump j 2 (w*(M'*U)^2)
lemma orbitsR (hD :0≤D) (i:E) (hx :‖i‖ < U) : Brush k (keenR k p D v w U) U⁻¹ (goreR τ ρ) i := by
  let z:R:=0; let Y:=M*U; let x:=U⁻¹ • i; let a:=((0:ℝ),x); let g :=hpoint ρ U z
  have hp':0≤p:= (h 0 (by simpa using hu)).nonneg; have hy:0 < Y:= mul_pos (by unfold spanV; positivity) hu
  have hx : ‖a‖ <1:= by apply max_lt (show ‖(0:ℝ)‖<(1:ℝ) by simp) ; unfold a x; rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr hu).le,mul_comm,← div_eq_mul_inv]; exact (div_lt_one hu).2 hx
  obtain ⟨hB,hG⟩:= springsP h hu hs hp (show ‖z‖ ≤ D from norm_zero.trans_le hD) hj a hx
  let P i:=Y⁻¹ • g i; let W i:= τ (g i)-τ 0-Z (g i); let T i:=Z (g i)
  have hm x:Y • P x=g x:= smul_inv_smul₀ hy.ne' _
  have he:Brush k (clump k 2 (w*Y^2)) 1 W a:= (composite hB (hL (P a) hG)).shimmy (Eventually.of_forall fun i=>by change _= τ (Y • P i)-_ - _; rw [hm])
  have hh:Brush k (Y*2) 1 g a:=by have hp:=hB.smul Y; rw [Real.norm_of_nonneg hy.le] at hp; exact hp.shimmy (Eventually.of_forall fun i=> (hm i).symm)
  have hw:= (hh.report Z ht).gathering he; apply reverseR hu; exact (skim x ((show a=(0,0)+hook E x by simp [a]) ▸ hw) (n_hook (E:=E))).shimmy (Eventually.of_forall fun i=>by simp only [Function.comp_apply,W,g,hpoint,goreR,z,smul_zero,add_zero,Prod.snd_add,ContinuousLinearMap.inr_apply, zero_add]; abel) -- markArc ℝ only. v adapt
end YM.QCD.Oasis
