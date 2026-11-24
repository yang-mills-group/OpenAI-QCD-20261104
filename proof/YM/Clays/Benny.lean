import YM.Clays.Inks
import YM.Clays.Norian
import YM.TIPS.Humbug
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample
open QCD QCD.Grass QCD.Cove Lattice Finset Ribbon Cupola Stew
open Function Lattice Wilson Creek Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Plate Plate.Card Relight Ruby Massive.PCAC
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
namespace Basal
variable {c:Side}{N:ℕ}{I D:Type}[Fintype I]{a C t b w x v θ m:ℝ}
variable (o:I→Site c)(p:I→Lat.Fields c 6→L[ℂ]Lat.Fields c 6) (H:∀ i,Veins (o i) (p i) C) (s:List I)(d:I→ℂ)
local notation "P"=> Patio (Keys c 6⊕Spine I)
local notation "M"=> ample 6 I
local notation "T"=> traceI I
local notation "Λ"=> Keys c 6
local notation "K"=> actE o p H d s
local notation "Γ"=> effect o p H d
local notation "amt" j:arg=> (s.filter (fun i=> i∈ (j:Finset I)))
variable (F: Reel c 6 I D) {U:BudgetPoint}
set_option quotPrecheck false
local notation "B!"=> U.B
-- W debit formula.Hit.Φ_F.e of E with gap.I.Blue
variable (f:D→Site c)(g:D→ℝ)(h:ValidX o F f g U t)
local notation "E"=> Oper o s F
local notation "Ψ"=> clayR o p H s d F
open ConnectedActivityE6 Blaze King Reserves
variable (hr: ∀ i:I, ‖d i‖≤a)(ha:0≤a)(hC:0 ≤ C)(ht:0<t)(hs:s.Nodup)
include ha hr hC ht hs H
local notation "ψ"=> extreme o s F g U a C
-- charge on all nonempty including new singles. reach Anchor.Light.By exterior words ∑.
variable (Ft:ℕ) (hf:Fires o Ft)(ε:ℝ)(he:0<ε)(u T':ℝ)(hV:Ac.Hit (fun i=>(F.addr i).support) U.B g (v+2*ε) T')
local notation "A₀"=> absP U.B U.order U.power Ft ε (C*a)*T'
omit ha hr hC ht hs H
local notation "ro"=> rootR (Spine I) Λ
variable (X: Gem c 6 D)
local notation "A!"=> source X I
variable (hq:∀ i,shadeG (X.view i))(hW:∀ i,Woven (X.addr i).site (X.addr i).support U t (X.view i) (g i))
local notation "V!" i:arg=> (X.addr i).site
variable (b' W:ℝ)(hp:Footprint.Anchored (fun i=>(X.addr i).site) g (fun i=> coverNumber U.B (X.addr i).support) b' W)
local notation "Ω"=> Oper o s A!
local notation "ΣE"=> clayR o p H s d A!
local notation "Bp!"=> absP U.B U.order U.power Ft ε (C*a)
open Cape
local notation "Lz"=> Taxing.birthV ΣE U.threshold
local notation "hue"=> vesta o Lz t
local notation "out"=> Oper o s A!
-- ~ deterministic failure receipts. use only finite Σ_.
instance [Fintype D] : Fintype (Oper o s F):=by unfold Oper; infer_instance
instance [Countable D] : Countable (Oper o s F):=by unfold Oper; infer_instance
local notation "ψ'"=> extreme o s A! g U a C
variable (hK:∀ i V,Stew.Sen ((X.addr i).site) t (X.view i V) ≤ g i)
include ht H hW hs hq
lemma filled [Fintype D] (V:Grid c) : K (ro (∑ i,X.view i V))= ro (∑ i,X.view i V)+(ΣE).rope U.threshold V+ withdraw 6 o t (swarm (hue) V):=by
      have hb:= pricesY o g ht X hq hW; have ht'(i:D):K ((A!).mark i V)=(A!).mark i V+ ∑ j: ↥(matings o s A! i),(ΣE).mark ⟨i,j⟩ V:= compass o p H s d A! _ _ hb V hs i; have hVK: K (ro (∑ i,X.view i V))=ro (∑ i,X.view i V)+ ∑ i:out,(ΣE).mark i V:=by
           rw [map_sum,map_sum,show (∑ i:out,(ΣE).mark i V) = ∑ i:D,∑ j:↥(matings o s A! i),(ΣE).mark ⟨i,j⟩ V from ?_, ←sum_add_distrib]; rotate_left; · let g(i:out):= (ΣE).mark i V; have hf:Summable g:=Summable.of_finite; exact (tsum_fintype g|>.symm : ∑ i:out,g i= ∑' i,g i).trans (hf.tsum_sigma.trans ((tsum_fintype (fun j:D=>∑' i',g (⟨j,i'⟩:out))).trans (sum_congr rfl fun i _=>tsum_fintype ..)))
           apply sum_congr rfl; exact fun i _=> ht' i
      rw [hVK,add_assoc]; apply congr_arg
      unfold Reel.rope swarm; rw [tsum_fintype,tsum_fintype,map_sum,←sum_add_distrib]; refine sum_congr rfl fun i _=>?_ ; let x:= (ΣE).mark i V; let z:= (ΣE).mist U.threshold i V; change x=z+ withdraw 6 o t (banknote 6 o t (x-z)); rw [Cupola.home _ _ _ ht]; abel
include ha hr hC hp hf he hK
local notation "Wb"=> Bp!*(anth ε (v+2*ε) U.B * W)
set_option maxHeartbeats 570000 in
lemma brick (hhV: v+4*ε≤ b')(hP':1 ≤ t)(hX:0 ≤ v)(hQ:hullP U.B Ft*(C*a)≤ ε) : (ΣE).Occupant o T t U 2 v Wb (fun _=>1)∧ Wax hue U.threshold U.B v Wb t ∧ (∀ i, shadeG ((hue).mean i)) ∧ ∀ i V,Mint 6 o t T ((ΣE).z i) ((hue).mean i V):=by
     have hP:=pricesY o g ht X hq hW; have hT:=(extracted o p H s d g hr ha hC ht hs Ft hf ε he X hq hW b' W hp hhV hP' hX hQ).1; have hz:= Taxing.onBirth o T ΣE (t:=U.threshold) hT.booked
     have hA : Ac.Hit (fun i=> ((ΣE).addr i).support) U.B ψ' v Wb:=pricing o p H s d A! _ _ hP hr ha hC ht hs Ft hf ε he _ (roots g ε he X hW b' W hp _ (by linarith) (by linarith)) hQ -- ν implicit inferred? ensure. 
     let D' := banknote 6 o t; refine ⟨hT,⟨vespers o T Lz (v:=t) hz,ψ',hA,fun i V=> ?_⟩,fun i V g=> congr_arg Subtype.val ((Cupola.across 6 o t T _ g _ (hz.shades ..).1).symm.trans (congr_arg D' (hz.paint ..))),fun i V=>Mint.initiate _ ht _ (hz.shades ..).1⟩
     let i0:=i.fst; let Y:= (X.addr i0).support; let u:= X.view i0 V; let w:= (ΣE).mark i V; change ‖token _ _ _ (banknote _ _ _ (w-masked U.threshold Y ((ΣE).mark i) V))‖ ≤_
     by_cases hv:Healthy U.threshold Y V; · rw [masked_eq _ _ _ _ hv,show w-_=0 from sub_self w,map_zero,map_zero,norm_zero]; exact mul_nonneg (by unfold taste Plate.reFee; positivity) (mul_nonneg (pow_nonneg (mul_nonneg hC ha) _) (hW _|>.travel)) -- version constants X
     rw [masked_ne _ _ _ _ hv,sub_zero,from_full o ht w]; let l':= s.filter fun j=> j ∈i.2.val; have hf:= price_all o p H d ht hr ha hC l' (ro u); have hg: Stitch.Tablet.credits t (ro u)=load (fun _=>t) (light _ u):=by
             have he: pluck Λ (burst T ∅) (ro u)=light _ u:= congr_fun (centers (I:=I) X i0) V -- syntax inspect
             have hh: Polite T ∅ (ro u):= (hP.costume i.1 _).1; exact (Stitch.Tablet.polite_bill ∅ _ hh ht).trans (congr_arg (load (A:=Λ) (fun _=>t)) he)
     have hu:l'.length=i.2.val.card:=payScope s hs _ ((outline o p H s A! _ _ hP _ _ i.2.2).1); rw [hg,hu] at hf; refine hf.trans (le_trans (mul_le_mul_of_nonneg_left (show load (fun _=>t) (light _ u)≤ g i.fst from (Stew.shot (Stew.lens _) _ _ ht).trans (hK _ _)) (pow_nonneg (mul_nonneg hC ha) _)) ?_) -- shot
     apply le_mul_of_one_le_left (mul_nonneg (pow_nonneg (mul_nonneg hC ha) _) (hW _|>.travel)); exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by simp)) (one_le_pow₀ (by simp))
end Basal
end YM.MassiveQCD.Sample
#print axioms YM.MassiveQCD.Sample.Basal.brick
