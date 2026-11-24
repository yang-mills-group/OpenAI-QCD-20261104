import YM.Kwick.Ledger
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Massive.Poised.Plans.Stamp.Stair
open Filter Function Set Lattice Wilson RG Module TensorProduct
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical
open QCD QCD.Lat QCD.Grass UV Poised Poised.Beacon Poised.Display Poised.Stative Poised.Sieve
open Finset Tawny Tawny.Cast Tawny.Cast.Rays Tawny.Cast.Carnal Tawny.Cast.Perla Tawny.Cast.TableT Tawny.Cast.Zinc
open Oriole Counting Counting.Click
local notation "Z"=> RawVec 10
local notation "T"=>Grade
variable {U:Type} (x y:Z)(i:Axis)(p:Rings 10)(k:Fin 4)(Pt Q:BudgetPoint)(w w' r v A ε C u t ε':ℝ)
private lemma rungG (g:Grade)(i:Fin 4): tierQ i=g→ g.1=8∨g.1=10:=by intro h; rw[← h]; fin_cases i <;> decide
private lemma footingS(j:Fin 4)(h:j≠0): (tierQ j).1=10:=by revert h; fin_cases j<;> decide
lemma bytes (q:Jars 10)(h:weightJ q <10 ∧ q.val ≠ tierQ 0) : princS (x.val i) q Pt w=0:=by
     -- weird weight 9 possible phase.Traces actually zero from grade catalogue
     have he:vaultP q.val x=0:=spec0 _ _ (fun i he=>by
           by_cases hp:i=0; · apply h.2; rwa[hp] at he
           have H:weightJ q=10:=(congr_arg Prod.fst he).trans (footingS _ hp); omega)
     unfold princS; rw [show gradeCut 10 q.val (x.val i)=0 from congr_fun (congr_arg Subtype.val he) i]; unfold wealth; simp only [Submodule.coe_zero, fare,map_zero,norm_zero,sum_const_zero]
local notation "lQ"=> weightJ
lemma byWeight(k:Fin 4) (hA:0≤A)(hu:0≤u) : (∑ j∈ Finset.univ.filter (fun j:Jars 10=>weightJ j<(tierQ k).1), A*u^weightJ j *princS (x.val i) j Pt w) ≤ if k=0 then 0 else A*u^8*wages i (stack 0 Pt.threshold w x):=by
     by_cases h:k=0
     · rw [if_pos h,sum_filter]; apply le_of_eq; refine sum_eq_zero fun j _=>?_ ; split; next hb=> rw [bytes]; rw[mul_zero]; have ht:(tierQ k).1=8:= h.symm ▸ rfl; rw [ht] at hb; exact ⟨by omega,fun hh=>by rw [show weightJ j=8 from congr_arg Prod.fst hh] at hb; contradiction⟩ -- args he in order
       next _=>rfl
     rw [if_neg h,footingS k h]; by_cases hp: tierQ 0∈ gradeS 10
     · let j:Jars 10:=⟨tierQ 0,hp⟩; rw[sum_eq_single j]; exact Eq.le (congr_arg ( (A*u^8) * ·) (worth_cash x i 0 w Pt.threshold))
       intro b hb hv; rw [bytes _ _ _ _ b ⟨(mem_filter.mp hb).2, fun h=> hv (Subtype.ext h)⟩,mul_zero]
       intro ht; exact (ht (mem_filter.mpr ⟨mem_univ _,by change 8 < 10; omega
                                ⟩)).elim
     have hz:=mul_nonneg (mul_nonneg hA (pow_nonneg hu 8)) (show 0≤wages i (stack 0 Pt.threshold w x) from sum_nonneg fun i _=> norm_nonneg _); rw [sum_eq_zero]; exact hz; intro j hj; rw [bytes _ _ _ _ _ ⟨(mem_filter.mp hj).2, fun h'=>hp (h' ▸ j.property)⟩,mul_zero]
local notation "ϕ" x:arg j:arg=> x.val j
-- basis-wise
lemma chartGr : chartL Pt w p (x.val i)=(stitchQ p Pt.threshold w:ℂ)* grunt p i x:=bLoom ..
lemma payGr (h:crest p.val=tierQ k): chartL Pt w p (x.val i)=grunt p i (stack k Pt.threshold w x):=by rw [chartGr,stack,map_smul,bet,read_p,if_pos h,smul_eq_mul,stitch_up _ _ _ _ h]
variable (h:TypeBeta u w w' (r*w') A ε ε' Pt Q (x.val i) (y.val i))(hA:0≤A)(hu:0≤u)(he:0≤ε)(hp:0<w)
include h hA hu he hp
local notation "d₀"=> wages i (stack 0 Pt.threshold w x)
local notation "W"=> wealth (x.val i).val Pt.threshold w
local notation "R"=> bud k Q.threshold (r*w')/bud k Pt.threshold w
lemma rank_fee2 (p:Rings 10): ‖grunt p i (stack k Q.threshold w' y- (↑(u^(tierQ k).1 * R):ℂ) • stack k Pt.threshold w x)‖ ≤ (if k=0 then 0 else A*u^8*(d₀))+ ε*W + ε':=by
      let f:= grunt p i; let z:ℝ:= (if k=0 then 0 else A*u^8*(d₀)); rw [map_sub,map_smul,smul_eq_mul]; by_cases h':crest p.val=tierQ k
      · rw[← payGr _ _ _ _ Q w' h',← payGr _ _ _ _ Pt w h']; have ht:= fare_lane (x.val i) (y.val i) p h hu hA he; rw [show UV.weight p.val=(tierQ k).1 from congr_arg Prod.fst h'] at ht
        have hf: chartL Q (r*w') p (x.val i)= (R:ℂ)* chartL Pt w p (x.val i):=by rw [chartGr,chartGr,stitch_up _ _ _ _ h',stitch_up _ _ _ _ h']; push_cast; rw [←mul_assoc,div_mul_cancel₀ _ (by have he:0<bud k Pt.threshold w:=mul_pos (pow_pos Pt.threshold_pos _) (pow_pos hp _); exact_mod_cast he.ne')]
        rw [hf, ← mul_assoc ((u:ℂ)^_)] at ht -- u maybe syntax
        rw [Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_div]; exact ht.trans (add_le_add_left (add_le_add_left (byWeight x i Pt w A u k hA hu) _) _) -- directions
      unfold stack bet; rw [map_smul,map_smul, read_p,read_p,if_neg h',smul_zero,if_neg h',smul_zero,mul_zero,sub_zero,norm_zero]; have hz0:0 ≤ ε':=by obtain ⟨g,hu,h⟩:=h.paid; exact (wealth_ge ..).trans h
      refine add_nonneg (add_nonneg ?_ (mul_nonneg he (wealth_ge ..))) hz0; exact ite_nonneg le_rfl (mul_nonneg (mul_nonneg hA (pow_nonneg hu 8)) (show 0 ≤ wages i _ from sum_nonneg fun i _=>norm_nonneg _))
local notation "F"=> Fintype.card (Rings 10)
lemma rhythmQ : wages i (stack k Q.threshold w' y - (↑(u^(tierQ k).1* R):ℂ) • stack k Pt.threshold w x) ≤ (F:ℝ)*((if k=0 then 0 else A*u^8*(d₀)) + ε* W+ ε'):=by
      apply le_trans (sum_le_sum (fun p _=> rank_fee2 x y i k Pt Q w w' r A ε u ε' h hA hu he hp p)); simp only [sum_const,nsmul_eq_mul,card_univ]; exact le_rfl
end YM.Massive.Poised.Plans.Stamp.Stair
#print axioms YM.Massive.Poised.Plans.Stamp.Stair.rhythmQ
