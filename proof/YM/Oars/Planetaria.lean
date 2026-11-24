import YM.Oars.Lavender
import YM.Oars.Reseats
import YM.Oars.Come
import YM.Cardinal.Girdle
/-!
 # Spaced cube publication (higher incidence E exports through an option swizzle,
 including true overhead income). Remainders store priors on right-stamps.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample
open QCD QCD.Grass QCD.Cove Lattice Finset Ribbon Cupola
open Function Lattice Wilson Creek Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Plate Plate.Card Relight Ruby
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {A B C I J E :Type}[Fintype A][Fintype B][Fintype I][Fintype J]
variable (A) (q:I→Bool)(p:J→Bool)(f:I→Option J)(g:I→J→ℝ)
local notation "R"=>Spine I
local notation "S"=>Spine J
variable (r:I→J→Prop) {P:Set (Finset J)} {D:Set (Finset I)}(hp:Pledge q p r P D) {c:Side}{N:ℕ} {a b w A₁ :ℝ}{m k i0:ℕ}(x:I→Site c)(y:J→Site c) (θ:ℝ)
include hp
local notation "M"=>Keys c 6
local notation "T"=> Patio (M⊕R)
local notation "L" j=>leaves M q p (findV r j) g
local notation "F" j=>flame M q p (findV r j) g
local notation "↑I"=>banknote 6 x θ
local notation "↑J"=>banknote 6 y θ
local notation "↓J"=> withdraw 6 y θ
local notation "↓I"=>withdraw 6 x θ
local notation "Γ" a=>loft r P a
namespace LoomT
open Massive.Poised.Plans Massive.Poised.Plans.Girdle
variable (P₀:I→Support c) (Pt:BudgetPoint) (G: Reel c 6 I E) (hG:G.Book x q)(hQ:∀ i, G.z i⊆ atlas P₀ (G.addr i).support)
local notation "Eⁱ"=> Fellows G r P
local notation "G'"=> swirl (P:=P) q p g r G
variable (hv:∀ i j,r i j→ y j∈P₀ i) (Bv:ℕ)(hα:∀ i,(opts r i).card≤Bv)(hΓ:∀ i j,r i j→ |g i j|≤a)
variable (F₁:E→ℝ)(hV:∀ i,∀ j∈G.z i,Sight (G.addr i).support (x j) k Pt θ (Reel.speaker q G i) (F₁ i))
local notation "Ξ"=> Girdle.tariff i0 k Pt.power Pt.order
variable (hΨ:∀ i j,r i j→ separation (x i) (y j) ≤ i0)(ht:0<θ)
open ConnectedActivityE6
-- rays price returns mixed E with fixed.Sight.Sever.PT.
section light
variable {G r} (Q:Reel c 6 J C)
omit hp
noncomputable abbrev LargeE:= {i:C // 2 ≤ (Q.z i).card}
noncomputable def survived : Reel c 6 J (LargeE Q):=⟨Q.addr ∘ Subtype.val, Q.z∘Subtype.val, Q.mark∘ Subtype.val⟩
include Q
lemma true_multi (h:Q.Book y p): (survived Q).Book y p:=by exact ⟨fun i=>h.stays i.val,fun i=>h.stamp i.val,fun i=>h.permit i.val,fun i=>h.room i.val,fun i V=>h.stage ..,fun i=>h.tint i.val⟩
end light
variable {Ξr v:ℝ}
variable (hY: Ac.Hit (fun i=> (G.addr i).support) Pt.B (Reel.choicePay (Reel.changeFare 6 (fun _=>Bv*a) G F₁) (fun i=> 2 ≤ (G.z i).card)) Ξr v)
local notation "S!"=> survived G'
include hp hQ hv hY hα hΓ hΨ ht hG hV
lemma divers (ht':0≤a): (survived (swirl (P:=P) q p g r G)).Occupant y p θ Pt k Ξr (Ξ*v) (fun _=>1):=by
   have hk (k:Eⁱ): k.snd.val.card=(G.z k.fst).card:= worldM _ hp.mast _ ((swipeL r G k).1) _ (swipeL ..); let τ:= tariff i0 k Pt.power Pt.order; have hs:0≤τ:=(by unfold τ tariff Girdle.shift; positivity); have ha:0 ≤ Bv*a:= mul_nonneg (Nat.cast_nonneg _) ht'; let Wv(i: Eⁱ):=(Ξ * F₁ i.fst)*‖Sample.purse (findV r i.snd.val) g (G.z i.fst)‖
   let hm:= ordained q p g r hp x y P₀ G hG hQ hv; have hF i:0≤F₁ i:=by obtain ⟨j,h⟩:= hG.stays i; exact (hV i j h).travels
   have hz k:0≤ Wv k:=by unfold Wv; exact mul_nonneg (mul_nonneg hs (hF _)) (norm_nonneg _)
   refine ⟨true_multi p y _ hm, fun i=> Wv i.val,?_,fun i j hj=>reads q p g r hp x y θ Pt _ hG _ F₁ hV hΨ ht j (show _ from hj)⟩ -- mφ
   intro x'; let Z:= LargeE (G'); let Ψ:Z→ℝ:= fun i=>if x'∈(G.addr i.val.fst).support then (∏ j∈i.val.snd.val,|(1:ℝ)|)*Wv i.val*Real.exp (Ξr *(coverNumber Pt.B (G.addr i.val.fst).support)) else 0; have hP i:0≤Ψ i:= by unfold Ψ; split; exact mul_nonneg (mul_nonneg (prod_nonneg fun _ _=> abs_nonneg _) (hz i.val)) (Real.exp_nonneg _); exact le_rfl -- simplify
   let f(i:E):= (Reel.choicePay (Reel.changeFare 6 (fun _=> Bv*a) G F₁) (fun i=>2 ≤ (G.z i).card)) i
   let f'(i:E):=if x'∈ (G.addr i).support then f i * Real.exp (Ξr*(coverNumber Pt.B (G.addr i).support)) else 0; have hS:= budget_scale hs (hY x'); change SumBudget Ψ _; apply budget_fiberwise (fun i:Z=>i.val.fst) hP _ hS
   intro i u he
   let p:= loft r P (G.z i); by_cases ht:2 ≤ (G.z i).card; swap
   · have hUp:u=∅:=Finset.eq_empty_iff_forall_notMem.mpr (fun j hj=>ht ((he j hj) ▸ hk j.val ▸ j.property))
     rw [hUp,sum_empty]; exact hS.1 i
   let Fj(j:↥p):Eⁱ:=⟨i,j⟩; let F'(j:↥p):Z:= ⟨Fj j,(hk (Fj j)).symm ▸ ht⟩; have he':Injective F':= fun x y he=> Sigma.mk.inj_iff.mp (Subtype.ext_iff.mp he)|>.2|> eq_of_heq
   have hh:u⊆ Finset.univ.image F':=by rintro ⟨⟨z,j⟩,h⟩ hj; have H:z=i:= he _ hj; subst i; exact mem_image_of_mem F' (mem_univ j)
   apply (sum_le_sum_of_subset_of_nonneg hh (fun j _ _=>hP j)).trans; rw [sum_image he'.injOn]; change (∑ j: ↥p,Ψ (F' j)) ≤ τ*f' i; unfold f'; split
   next hA=>
      have h(j): Ψ (F' j)=(τ*F₁ i)*‖purse (findV r (j:↥p).val) g (G.z i)‖ * Real.exp (Ξr*((coverNumber Pt.B (G.addr i).support))):=by unfold Ψ; rw [if_pos hA]; unfold Wv; simp only [abs_one,prod_const_one,one_mul]; rfl
      simp_rw [h]; rw [← Finset.sum_mul,←Finset.mul_sum]; change _≤τ*(_*_); unfold f Reel.choicePay Reel.changeFare; rw [if_pos ht]; dsimp only; rw [abs_of_nonneg ha, Finset.prod_const]; apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ((sum_coe_sort p (fun j=>‖purse (findV r j) g (G.z i)‖)).trans_le (duties g r hp.mast Bv hα (G.z i) (fun i _=>hΓ i) ht')) (mul_nonneg hs (hF i))) (Real.exp_nonneg _)).trans_eq; ring
   next hA=>
      rw [mul_zero]; rw [sum_eq_zero fun i hi=>?_]; exact if_neg hA -- defeq?
-- passage on permitted sets.La launch. 
omit hQ hv hY hα hΓ hΨ ht hV
lemma wisps (b':ℝ)(V:Grid c)(h:Summable fun i=> ‖G.mist b' i V‖): Summable fun i:Eⁱ=> ‖(G').mist b' i V‖:=by
    let f (i:E):=G.mist b' i V; let k:Finset J→ℝ:= fun j=> ‖(F j).toLinearMap.toContinuousLinearMap‖; let K' i:= ∑ j:Finset J,k j*‖f i‖; have hf(k:Eⁱ):(G').mist b' k V=(F k.2.val) (f k.1):=by
        unfold Reel.mist f; by_cases h:Healthy b' (G.addr k.1).support V; · rw [masked_eq _ _ _ _ (show Healthy _ ((G').addr _).support V from h),Reel.mist,masked_eq _ _ _ _ h]; rfl
        rw [masked_ne _ _ _ _ (show ¬ Healthy _ ((G').addr _).support V from h),Reel.mist,masked_ne _ _ _ _ h,map_zero]
    apply (summable_sigma_of_nonneg (show _ from fun i:Eⁱ=> norm_nonneg ((G').mist b' i V))).2; refine ⟨fun _=>Summable.of_finite, Summable.of_nonneg_of_le (fun _=>tsum_nonneg fun _=>norm_nonneg _) (fun i=>?_) (show Summable K' from summable_sum fun j _=>h.mul_left _)⟩
    let Z:=Γ (G.z i); rw [tsum_fintype]; simp_rw [hf]; change ∑ j: ↥Z, ‖(F j.val) (f i)‖ ≤ _; exact (sum_le_sum (g:=fun j=>k j.val*‖f i‖) fun j _=>(F j.val).toLinearMap.toContinuousLinearMap.le_opNorm _).trans ((sum_coe_sort Z (fun j=> k j*‖f i‖)).trans_le (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=>mul_nonneg ((F i).toLinearMap.toContinuousLinearMap.opNorm_nonneg) (norm_nonneg _)))) -- bind scope k
lemma allure (b':ℝ)(V:Grid c)(h:Summable fun i=> ‖G.mist b' i V‖)(u:Finset J)(he:u∈P) : shutter M u ((G').rope b' V)=(F u) (G.rope b' V):=by
    let v(i:E):=G.mist b' i V; let k : Finset J→ T → Patio (M⊕S):= fun j x=> (F j) x; let Z:= shutter M u; have hf(j:Eⁱ):(G').mist b' j V= k j.snd.val (v j.fst):=by
        unfold Reel.mist v; by_cases ht:Healthy b' (G.addr j.fst).support V; · rw [masked_eq _ _ _ _ (show Healthy _ ((G').addr _).support _ from ht),Reel.mist,masked_eq _ _ _ _ ht]; rfl
        change _ = (F _) _; rw [masked_ne _ _ _ _ (show ¬Healthy _ ((G').addr _).support _ from ht),Reel.mist,masked_ne _ _ _ _ ht,map_zero]
    let f(i:Eⁱ):=(G').mist b' i V
    have hg:Summable f:=(wisps q p g r hp x G hG b' V h).of_norm
    change Z.toLinearMap.toContinuousLinearMap (∑' i:Eⁱ,f i) = (F u).toLinearMap.toContinuousLinearMap (∑' i,v i); rw [ContinuousLinearMap.map_tsum _ hg,ContinuousLinearMap.map_tsum _ h.of_norm,(Z.toLinearMap.toContinuousLinearMap.hasSum hg.hasSum).summable.tsum_sigma]; refine tsum_congr fun i=> ?_ -- api summable.LMap.
    rw [tsum_fintype]; let Px:= Γ (G.z i); change ∑ j:↥Px,Z (f _)=(F u) (v i); unfold f; simp_rw [hf]; have hv: Polite q (G.z i) (v i):=by
         unfold v Reel.mist; by_cases he:Healthy b' (G.addr i).support V; · rw [masked_eq _ _ _ _ he]; exact (hG.stage ..).1
         rw [masked_ne _ _ _ _ he]; exact polite_nil ..
    exact (sum_coe_sort Px (fun x=>Z (k x (v i)))).trans ((map_sum Z ..).symm.trans (fareSum M q _ _ r hp he _ _ hv))
end LoomT
end YM.MassiveQCD.Sample
