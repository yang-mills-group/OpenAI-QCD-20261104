import YM.Intag.Reclaim
import YM.Intag.Vail
/-! # Inversion over all nonempty subsets.Pass matrices.Y.T real linear estimate.Rule.B.Y.Toolkit
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample.Quills
open QCD QCD.Grass QCD.Creek QCD.Cove Function Finset Filter NormedSpace
open MassiveQCD.Ribbon MassiveQCD.Play MassiveQCD.Play.Chamber Apron Cupola
open scoped Topology ContDiff BigOperators Classical TensorProduct Matrix.Norms.L2Operator
open YM.Arise.Bill YM.Arise.Count YM.Massive YM.Massive.UV Quills.Eden YM.Massive.Lyre
variable {A B I J:Type}[Fintype A][Fintype B][Fintype I][Fintype J]{n:ℕ}
namespace Clover
variable (Q:I→Bool)(v:I→ℕ)(P: ∀ i:I, Arise.Bill.Cups (v i) (Q i))(p:I→ E4)
local notation "Z"=> pays (U:=A) Q v p P
variable (i:Finset I)
local notation "R"=> Spine I
local notation "Kv" i:arg=> Quills.tour i
-- invert costs. K+, subtract log.
lemma gratis : (pays (U:=A) Q v p P) ∅=1:=by unfold pays; rw [prod_empty, Vest.Tone.read,Bera.alights,map_one]
variable (L:List I)(hL:L.Nodup)(U:I→Alg A)(hU:∀ i,Hom (Q i) (U i))(ht:Set.InjOn p L.toFinset)
local notation "Q!"=> wordA Q p v U hU P
local notation "Xt"=> L.toFinset
local notation "W"=>cupZ Q v P p
noncomputable abbrev hats (i:Finset I):Patio (A⊕Spine I):= kits i (fun i=> Lyre.emitK Q i (U i) (hU i)) (fun i=> -cetacea Z i)
local notation "Y"=> hats Q v P p U hU
variable (s:Fin n→I)(B : Finset I)(hv:Set.InjOn p B)
include hv
lemma chorusBills : hats Q v P p U hU B*(∑ i∈B.powerset, (pays (U:=A) Q v p P) i)= NormedSpace.exp (∑ i∈B,emitK Q i (U i) (hU i)):=by
     let f:=cetacea Z; let x := ∑ i∈ B.powerset.erase ∅, f i
     have he: exp x= ∑ i∈B.powerset,(pays (U:=A) Q v p P) i:=by
          refine (Play.Chamber.source _ B (?_ :∀ i∈ B.powerset, f i∈ VaultP A Q i)).trans (?_)
          · intro i hi; obtain ⟨h,hc⟩:=cents Q v P p B hv i (mem_powerset.mp hi); change cetacea Z i∈_; rw [← hc A]; exact h A
          exact sum_congr rfl fun i _=> carries Z _ (gratis ..)
     unfold hats kits; rw [← he]; change _ * exp (∑ i∈ B.powerset.erase ∅,- f i)*_= _; rw[sum_neg_distrib, mul_assoc,← exp_add]; change _ * exp (-x+x) =_; rw [neg_add_cancel, exp_zero,mul_one]
lemma reducesG (hx:crest s ⊆ B): numbered Q A s ((Y) B)=wordA Q p v U hU P (List.ofFn s):=by
    let E:= crest s; let H(i:I):= emitK Q i (U i) (hU i); let t:= fun i=> -cetacea Z i
    let J:= shutter A E
    have he:J ((Y) B)= J ((Y) E):=by
         change J (kits B H t)= J (kits E H t); unfold kits; rw [map_mul,map_mul,map_exp J J.toLinearMap.toContinuousLinearMap.continuous,map_exp J J.toLinearMap.toContinuousLinearMap.continuous, map_exp J J.toLinearMap.toContinuousLinearMap.continuous,map_exp J J.toLinearMap.toContinuousLinearMap.continuous, map_sum,map_sum,map_sum,map_sum]; congr 2
         · symm; refine sum_subset hx (fun i hi hh=>?_); exact (stamen_h A Q {i} E (H i) (show Polite Q {i} (H i) from ⟨U i,rfl⟩)).trans (if_neg (fun hp'=> hh (hp' (mem_singleton_self _))))
         symm; refine sum_subset (show E.powerset.erase ∅ ⊆ _ from fun i hi=> mem_erase.mpr ⟨ne_of_mem_erase hi, mem_powerset.mpr ((mem_powerset.mp (mem_of_mem_erase hi)).trans hx)⟩) (fun i hi hh=> ?_)
         have ht : Polite Q i (t i):= Polite.minus (show Polite Q i _ from cens_log Q Z i (fun j hj _=>canon Q p P B hv _ ((hj.trans (mem_powerset.mp (mem_of_mem_erase hi)))) ))
         exact (stamen_h _ Q i E _ ht).trans (if_neg (fun he=>hh (mem_erase.mpr ⟨ne_of_mem_erase hi,mem_powerset.mpr he⟩)))
    rw [wordA, Lyre.verses Q, show (List.ofFn s).toFinset=E from ?_]
    exact congr_arg (signG Q s • ·) (phoenixC A _ _ E he _ (located Q E))
    ext i; simp only [E,List.mem_toFinset,List.mem_ofFn,exists_fix]
omit hv
noncomputable def saves (s:Fin n→I)(i:Finset I): ℂ:= signG Q s * Quills.Eden.flux Q i (crest s) (cupZ Q v P p i) * signG Q (tour (crest s \ i))
-- redefines binder
variable (h_v:Set.InjOn p (crest s))(hs: Injective s)
include h_v hs
local notation "Ψ"=> hats Q v P p U hU
lemma portionR (i:Finset I)(hi:i∈ (crest s).powerset) : numbered Q A s ((hats Q v P p U hU (crest s)) * (pays (U:=A) Q v p P i))=saves Q v P p s i • wordA Q p v U hU P (List.ofFn (tour (crest s \ i))):=by
     let t:=tour (crest s \ i); have ht:crest t=(crest s \ i):=club _
     obtain ⟨h,hQ⟩:= earn_l Q v P p i _ h_v (mem_powerset.mp hi)
     rw [←hQ]; let x:= (Ψ) (crest s); change signG Q s • pluck A _ (x*qraft _ _ _)= _; rw [salary Q i (crest s) _ x h (mem_powerset.mp hi)]; apply Eq.trans (by rfl)
     rw [← show numbered Q A t x = wordA Q p v U hU P (List.ofFn t) from (reducesG Q v P p U hU t _ h_v (show crest t ⊆ crest s from ht.symm ▸ Finset.sdiff_subset))]; let Ωb:= signG Q s; let u:= Quills.Eden.flux Q i (crest s) (cupZ Q v P p i)
     let b:=signG Q t; change Ωb • u • _= (Ωb*u*b) • (b • pluck A (burst Q (crest t)) x); rw [smul_smul,smul_smul (Ωb*u*b),mul_assoc (Ωb*u) b b,show b*b=1 from (arm_bill Q t (snug _)).2.1, mul_one,ht]
-- whole-coefficient Term yields free moment with order.Via multiplication by identity proof.
lemma deliver : numbered Q A s (hats Q v P p U hU (crest s) * (pays (U:=A) Q v p P (crest s)))=UV.Free.moment (v∘s) (points (p∘s)) (fun i=>meaning _ _ (P (s i))) • (1:Alg A):=by
     let Zr:= crest s; let i:=tour (Zr\Zr); let Y':=hats Q v P p U hU Zr; let F:=(pays (U:=A) Q v p P Zr); let t:= shutter A (∅:Finset I)
     have ht: t Y'=1:=by
          let Uq (i:I):=emitK Q i (U i) (hU i); unfold Y' hats kits; rw[map_mul,map_exp t t.toLinearMap.toContinuousLinearMap.continuous,map_exp t t.toLinearMap.toContinuousLinearMap.continuous,map_sum,map_sum, sum_eq_zero, sum_eq_zero,exp_zero,mul_one]
          rotate_left -- cost first?
          · intro i hi; exact (stamen_h _ Q {i} _ _ (show Polite Q {i} (Uq i) from ⟨_,rfl⟩)).trans (if_neg (by simp))
          intro i hi; have h:Polite Q i (-cetacea (pays (U:=A) Q v p P) i):=Polite.minus (show Polite Q i _ from cens_log Q (pays Q v p P) i fun j hj _=> canon Q p P _ h_v _ (hj.trans (mem_powerset.mp (mem_of_mem_erase hi))))
          exact (stamen_h _ Q i _ _ h).trans (if_neg (fun ht=>ne_of_mem_erase hi (subset_empty.mp ht)))
     have h(c:Fin n):s c∈(crest s):=(exists_fix ..).2 ⟨c,rfl⟩
     rw [← Arise.Bill.pay_f Q v p s P hs (show points (p∘s)∈conf n from fun i j e=> hs (h_v (h i) (h j) e))];
     let V:=cupZ Q v P p Zr; obtain ⟨hh,hx⟩:= earn_l Q v P p Zr _ h_v le_rfl; rw [← hx A]; let P_R:= qraft A _ V; change signG Q s • pluck A (burst Q Zr) (Y'*P_R)=signG Q s • pluck A _ P_R
     apply congr_arg (signG Q s • ·); rw [salary Q Zr Zr V Y' hh le_rfl, show pluck A (burst Q Zr) P_R=_ from (by rw [← salary Q Zr Zr V 1 hh le_rfl,one_mul]:pluck A (burst Q Zr) P_R= Quills.Eden.flux Q Zr Zr V • pluck A (burst Q (Zr\Zr)) 1)] -- fix syntax
     rw [Finset.sdiff_self]; apply congr_arg; exact phoenixC _ _ _ ∅ (ht.trans (map_one _).symm) _ (located Q ∅) -- arity ht.
lemma inverse_l : (List.ofFn (U ∘ s)).prod = UV.Free.moment (v∘s) (points (p∘s)) (fun i=>meaning _ _ (P (s i))) • (1:Alg A) + ∑ i∈(crest s).powerset.erase (crest s), saves Q v P p s i • wordA Q p v U hU P (List.ofFn (tour ((crest s)\ i))):=by
    let T:= crest s; have hh:= chorusBills Q v P p U hU _ h_v; rw [← show numbered Q A s (NormedSpace.exp (∑ i ∈ T,emitK Q i (U i) (hU i)))= (List.ofFn (U ∘ s)).prod from regalL Q s U hU _ (Finset.Subset.refl T) hs, ← hh, mul_sum,map_sum, ← add_sum_erase _ _ (mem_powerset_self (crest s)),deliver Q v P p U hU s h_v hs]; apply congr_arg; exact sum_congr rfl fun i hi=> portionR Q v P p U hU s h_v hs i (mem_of_mem_erase hi) -- arity.
end Clover
end YM.MassiveQCD.Sample.Quills
#print axioms YM.MassiveQCD.Sample.Quills.Clover.inverse_l
