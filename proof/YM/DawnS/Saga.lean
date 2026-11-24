import YM.DawnS.Grail
import YM.Next.MAXWELL.Core
set_option autoImplicit false
noncomputable section
namespace YM.DawnS
open Function Set Filter Finset Lattice Analysis MeasureTheory Tensor TensorProduct Maxwell Arise.Range Massive Massive.UV Massive.UV.Free QCD QCD.Lat Grass
open scoped Topology ContDiff BigOperators InnerProductSpace TensorProduct Classical Matrix ComplexOrder ENNReal
local notation "P"=> RingS
variable {d:ℕ}(q:Peak d→ℂ)(r:ℝ)(hr:0<r)(c:Bool)
local notation "η"=> sigL (d:=d) r
variable (k:Flavor 6)(i:Hue)
local notation "Φ"=> (∑ j,q j • UAtom k i c j)
include hr
lemma dawn2 : (2:ℂ)* η Φ Φ= ↑(∑ j:Pinor, ∫ z:PR, chargeP q c r j z ∂wa):=by
    rw [sparkSum q q c r k i hr]; push_cast; refine Finset.sum_congr rfl fun j _=>?_ ; rw[twinsP]; exact integral_ofReal ..
lemma pulse_non : 0≤η Φ Φ:=by
    have hv : (η Φ Φ)= ↑(∑ j:Pinor, ∫ z:PR, chargeP q c r j z ∂wa) / (2:ℂ):= eq_div_of_mul_eq (by norm_num) ((mul_comm ..).trans (dawn2 q r hr c k i)) -- ordered division ok?
    rw[hv]; apply div_nonneg ; exact_mod_cast (show 0≤∑ j:Pinor, ∫ z:PR,chargeP q c r j z ∂wa from sum_nonneg fun j _=> ahead q c r j hr); norm_num -- ℂ order not div
lemma lives (h:q≠0):0<η Φ Φ:=by
      refine lt_of_le_of_ne (pulse_non q r hr _ k i) (fun hc=>h (peakGone q r hr c ?_)); have hv:= dawn2 q r hr c k i; rw[←hc,mul_zero,←Complex.ofReal_zero,Complex.ofReal_inj] at hv; intro x hx b; exact shading q c r b hr ((sum_eq_zero_iff_of_nonneg (fun i _=> ahead q c r i hr)).mp hv.symm b (mem_univ _)) x hx
-- normalize list positive.any number. no universe leakage.
variable (g:Vault d→ℂ)
noncomputable def expandVt (g:Vault d→ℂ):beam d:=∑ i,g i • lantern i
abbrev CasksS:= Flavor 6 × Hue × Bool
noncomputable abbrev flattenCst(p:CasksS)(i:Peak d): Vault d := ((p.1,p.2.1,p.2.2,i):Vault d)
local notation "Y"=> expandVt g
noncomputable def excelT (p:CasksS): beam d:=∑ i:Peak d,g (flattenCst p i) • UAtom p.1 p.2.1 p.2.2 i
local notation "wP"=>excelT g
-- show expansion over p via sigma equivalence
omit hr in
lemma expandsS : expandVt g=∑ p:CasksS,wP p:=by
    unfold expandVt excelT; simp_rw[Fintype.sum_prod_type]
lemma foldedG : η Y Y=∑ p:CasksS, η (wP p) (wP p):=by
    rw[expandsS]; simp only [map_sum,LinearMap.sum_apply]; apply Finset.sum_congr rfl fun p _=>?_ 
    rw [Finset.sum_eq_single_of_mem p (mem_univ _)]; intro i _ hi; unfold excelT; simp only [map_sum,map_smul,map_smulₛₗ,LinearMap.sum_apply,LinearMap.smul_apply]; have h': (i.2.1,i.1,i.2.2) ≠(p.2.1,p.1,p.2.2):=by intro he; simp only[Prod.mk.injEq] at he; apply hi; ext1; exact he.2.1; exact Prod.ext he.1 he.2.2
    simp_rw[fun (a b:Peak d)=> ray_L hr _ _ _ _ _ _ a b h'];simp
lemma heartbeat (hv:g≠0):0<η Y Y:=by
    rw [foldedG r hr g];
    let f(p:CasksS)(i:Peak d):= g (flattenCst p i); have hP :∃ p:CasksS,f p ≠ 0:=by
         by_contra! h; apply hv; ext1 i; obtain ⟨a,b,c,x⟩:=i; exact congr_fun (h (a,b,c)) x
    obtain ⟨p,hp⟩:=hP
    exact (lives (f p) r hr p.2.2 p.1 p.2.1 hp).trans_le (Finset.single_le_sum (f:=fun i:CasksS=>sigL r (excelT g i) (excelT g i)) (fun i _=>pulse_non (f i) r hr i.2.2 i.1 i.2.1) (mem_univ p))
end YM.DawnS
