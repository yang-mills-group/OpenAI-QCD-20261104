import YM.Eole.Stock
import YM.Eole.Roots
/-! Sector exchange in the replica polynomial. Use ordered factors. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample.Eole
open QCD QCD.Grass QCD.Cove Lattice Finset Ribbon Cupola Stew Function
open Lattice Wilson Creek Lat Kit NormedSpace RG Cove Filter Run
open Loom Fleet MeasureTheory Ribbon Cupola Plate Ruby
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J A B:Type}[Fintype I][Fintype J][Fintype A][Fintype B]
open Quills
open Further.ShellBirth49.Fusing Collide
variable {E K:Type} {c:Side}
local notation "N"=> E⊕K
-- nodes indexed full exponent E and fully decomposed forced.
open QCD.GasP QCD.Struck
variable (W:Bloc I J) (g:E⊕K→ Finset I) (Y:K→Hat c)
open Sway OrbitG Bay Strut Push.Local Push.AbsoluteSums Ursell Gas Graph Patron Kites Ribbon Cupola Plate Plate.Card Relight Ruby Massive.PCAC
local notation "κ"=> Keys c 6
variable (q:I→ Bool) {P:BudgetPoint} {v α b t:ℝ}
open Further.ShellBirth49.Fusing Collide
variable (o:I→Site c)(p:J→Site c)
-- E raw footprint and common extensions
local notation "M"=> Patio ((Keys c 6)⊕Spine I)
local notation "Mt"=> Patio ((Keys c 6)⊕Spine J)
local notation "λt"=>W.flag q
variable (old:E→Support c)(a:E⊕K→Support c)(f:E⊕K→ Grid c→ Patio ((Keys c 6)⊕Spine I))(z:E⊕K→ℝ)
local notation "P₀"=> Grid c
set_option quotPrecheck false
local notation "T"=>P.threshold
local notation "A'"=>day f
local notation "H'"=>night old f T
local notation "S'"=> Support c
include W
variable (h:Setting W g Y q o p old a f z P t)
include h
open ConnectedActivityE6 Blaze King
local notation "L"=> Cand W g Y
local notation "G"=> Hard W g Y
local notation "Jr"=>journal W g q f
local notation "μ"=> lunarZ W g q old f
local notation "mT"=> ample 6 J
local notation "F'"=> feather W g Y q o p old a f z h
local notation "Z0"=> hats W g Y
local notation "WZ"=> Stretch.Basin (feather W g Y q o p old a f z h) (hats W g Y) P.threshold
local notation "Ω"=> Stretch.Orig (feather W g Y q o p old a f z h) (hats W g Y)
local notation "ξ"=> Stitch.Tablet.credits
local notation "Aξ"=> (swatch (E:=E) Y)
variable {ν w β δ y η ε π C:ℝ}
local notation "φ" => ν*(1-δ)⁻¹
variable (hp:1 ≤ v)(hT:1 ≤ t)
-- root grants.Titleα premise , supplies.
open Push.AbsoluteSums.Trees
variable (hw:1 ≤ w)(hz:Ready a P.B (QCD.GasP.taxed (swatch Y) z w) α ν b δ)(h0:0≤ α) (hη: 0 ≤ η)(hα:η+ε=α)(he:0 < ε)
local notation "Q'"=> W.flag q
local notation "U"=> withdraw 6 p t
local notation "Pν"=> φ
variable (hρ:0<ν*(1-δ)⁻¹)(hr:π<1) (hδ: degreePrice P.B (ν*(1-δ)⁻¹) ε ≤π)(hW:(ν*(1-δ)⁻¹)*(1-π)⁻¹ ≤1)
include hT hw hz h0 hη hα he hρ hr hδ hW
lemma journey : Wage.Tip 6 p (W.flag q) (Stretch.Basin (feather W g Y q o p old a f z h) (hats W g Y) P.threshold) P t η w:=by
    let hθ:=zero_lt_one.trans_le hT; have hx:Quits (F') P.B (Pν) w (η+ε) t:= hα.symm ▸ tariff W g Y q o p old a f z h hz hθ h0 hw
    exact Stretch.supportTip 6 p _ (F') (Z0) (stems W g Y q o p old a f z h) (fun i V=> (coinV W g Y q o p old a f z h hθ i V).launch) hx hw hη hρ he hr hδ hW
omit hη hα he hρ hr hδ hW
-- existence reaches. hF→ income.H' -- Y Loft sum
variable (x: Grid c)
lemma grows_sum : Summable (fun i:Hard W g Y=> ‖hardπ W g Y q (night old f T x) i‖) ∧ U (heartK WZ T x) =∑' i,gift (hardπ W g Y q (night old f T x)) Z0 (flags T x) i:=by
    let hh:=zero_lt_one.trans_le hT; let u:=hardπ W g Y q (night old f T x); let Y' (i:Hard W g Y) := (F').warp i x; have hx:=tariff W g Y q o p old a f z h hz hh h0 hw
    have ht(i:Hard W g Y) :u i= U (Y' i):=(Cupola.home _ _ _ hh _).symm; have hA : Summable fun i=>‖Y' i‖:= Ruby.income (F') x hT hw hx h0; have hX(i:Finset G): U (tK Ω T x i)= gift u Z0 (flags T x) i:=by
          unfold tK gift; simp_rw[GasP.close]; split_ifs with ht' hp hp; · rw[map_prod]; exact prod_congr rfl fun i _=> (ht _).symm
          · exact False.elim (hp ht')
          · exact False.elim (ht' hp)
          rw[map_zero]

    refine ⟨?_,?_⟩
    · change Summable (fun i=> ‖u i‖); simp_rw [ht]; exact Film.payable (U).toLinearMap.toContinuousLinearMap hA
    rw [Stretch.dreamed (F') (Z0) (stems W g Y q o p old a f z h) hw h0 hx hT x]; unfold heartK; have hB:Summable (fun i:Finset G=> tK Ω T x i):=by
             refine Summable.of_norm ((summable_finsetProd_of_summable_nonneg (fun _=> norm_nonneg _) hA).of_nonneg_of_le (fun _=>norm_nonneg _) (fun i=> ?_)); unfold Ruby.tK; split; exact Finset.norm_prod_le ..; rw[norm_zero]; exact prod_nonneg (fun _ _=>norm_nonneg _)
    exact ((U).toLinearMap.toContinuousLinearMap.map_tsum hB).trans (tsum_congr hX)
local notation "S"=> sachet W g Y q old a f P
local notation "XE"=> lucida W g Y q o p old a f z h
local notation "V"=> Cape.vesta p (S) t
variable (hX:(lucida W g Y q o p old a f z h).Occupant p (W.flag q) t P 2 β C (fun _=>1)) (hb:0≤ β)
include hX hb
lemma wings : Summable fun i=> ‖(XE).mist T i x‖:=by obtain ⟨f',hF,hG⟩:= hX.reserve; simp only [abs_one,prod_const_one,one_mul] at hF; exact (creditE p Q' XE _ hX.booked hG hF hb hT _).norm
lemma slim : HasSum (softπ W g Y q (night old f T x)) (Reel.rope XE T x + U (swarm V x)):=by
     have hm:=wings W g Y q o p old a f z h hT hw hz h0 x hX hb; have ht:= ((softly W g Y q o p old a f z h hw hz h0 (zero_lt_one.trans_le hT)).heated hT h0 x).1.hasSum; let H(i: Cand W g Y):= Reel.mist XE T i x; refine (hm.of_norm.hasSum.add ((U).toLinearMap.toContinuousLinearMap.hasSum ht)).congr_fun fun i=>?_ ; let u:= lunarZ W g q old f i.val P.threshold x; change u= H i+ U ((V).mean i x); rw [show U ((V).mean i x) =_ from (show _= (S).wick i x from Cupola.home _ _ _ (zero_lt_one.trans_le hT) _)]; change u=H i+(u-H i); abel
-- origin factors.
omit h hz h0 hw hX hb hT
set_option maxHeartbeats 600000 in
lemma lamps (x y:M)(hv: Polite q ∅ x) (hY:ValidPieces κ q univ y): Bloc.sparC κ q W (x*y)=Bloc.sparC κ q W x * Bloc.sparC κ q W y:=by
      rw[hY.wholeV,mul_sum,map_sum,map_sum,mul_sum]; let Tx:= Bloc.sparC κ q W; refine sum_congr rfl fun i _=>?_ ; let z:=Cupola.pick κ q i y; have hp : Polite q i z:=choseTuft ..; have hw :Polite q i (x*z):= Finset.empty_union i ▸ (hv.attached hp); by_cases ht:W.plant (W.core i)=i
      · let s:=W.core i; let ee:Finset J:=∅; have hx: W.plant ∅=(∅:Finset I):=biUnion_empty; have hz0:Polite q (W.plant s) z:= (show W.plant s=i from ht).symm ▸ hp; have hX: Polite q (W.plant ∅) x:= hx.symm ▸ hv; have h0: (∅:Finset J)∪s=s:=empty_union s; have hΦ:=Bloc.ribs κ q W ∅ s (disjoint_empty_left _) x z hX hz0; rw[h0] at hΦ; have h_xt:Polite q (W.plant s) (x*z):=by rw [show W.plant s=i from ht]; exact hw
        rw [Bloc.single_plant κ q W (x*z) h_xt,Bloc.single_plant κ q W x hX, Bloc.single_plant κ q W z hz0]; exact hΦ
      rw [Bloc.all_seed κ q W i _ hw ht,Bloc.all_seed κ q W i _ hp ht,mul_zero]
include h hz h0 hw hX hb hT
-- algebra K.Full Φ.
variable (K₀:Mt)
lemma rescale (z': Patio (Keys c 6))(hY:Summable fun i:E⊕K=> ‖night old f T x i‖):
    Bloc.sparC κ q W (rootR (Spine I) κ z' * (NormedSpace.exp (∑' i,night old f T x (Sum.inl i))*(∑' i,gift (night old f T x ∘ Sum.inr) Y (flags T x) i)))= rootR (Spine J) κ z' * (NormedSpace.exp (Reel.rope XE T x+U (swarm V x))* U (heartK WZ T x)):=by
      let u:= H' x; obtain ⟨hA,hD⟩:=grows_sum W g Y q o p old a f z h hT hw hz h0 x; have hL:= slim W g Y q o p old a f z h hT hw hz h0 x hX hb
      let Z':= ∑' i,gift (u∘Sum.inr) Y (flags T x) i; have hμ(i):Polite q (g i) (u i):=(glowing W g Y q o p old a f z h i x).1; let q' i:=u (Sum.inl i); have hQ:Polite q ∅ (rootR (Spine I) κ z'):=by unfold Polite; rw [burst_absent]; exact ⟨_,Ribbon.quiet ..⟩
      have hp:ValidPieces κ q univ (NormedSpace.exp (∑' i,q' i)*Z'):=by
          let v (i:N):= ValidPieces.role _ (hμ i) (subset_univ _); have hV:ValidPieces κ q univ Z':=by
                refine ValidPieces.tab (budgets Y (flags T x) (u ∘ Sum.inr) (hY.comp_injective Sum.inr_injective)).of_norm.hasSum ?_; intro i; unfold gift; split; next h=>
                            let s:Finset N:= (∅:Finset E).disjSum i; have hG:= paint_packets g q u hμ s; unfold s at hG; rw [prod_disjSum,Finset.prod_empty,one_mul] at hG; exact ValidPieces.role _ hG (subset_univ _)
                next _=> exact ValidPieces.noneV
          exact (ValidPieces.tab («U»:=univ) (hY.comp_injective Sum.inl_injective).of_norm.hasSum (fun i=>v (.inl i))).exponent.mul hV -- implicit edit
      let Sp:= NormedSpace.exp (∑' i, q' i)*Z'; rw [lamps _ _ _ _ hQ hp]; have ht:= paradigm W g Y q u (flags T x) hμ h.ear hY hL.summable.norm hA
      rw [Bloc.single_plant (s:=∅) κ q W _ (by simpa [Bloc.plant] using hQ), Bloc.planted_value]; refine congr_arg _ (?_ : Bloc.sparC κ q W Sp= _); exact ht.symm.trans (congr_arg₂ (·*·) (congr_arg NormedSpace.exp hL.tsum_eq) hD.symm)
end YM.MassiveQCD.Sample.Eole
#print axioms YM.MassiveQCD.Sample.Eole.journey
#print axioms YM.MassiveQCD.Sample.Eole.rescale
