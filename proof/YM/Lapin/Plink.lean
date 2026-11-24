import YM.Lapin.Olen
import YM.Lapin.Spark
/-! End read at reference upper Hop boot.Several charts transfer.X near arbitrary.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Massive.Patria.Gall.Cahoots
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical Kronecker InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
open Tawny Tawny.Cast Tawny.Cast.Rays Tawny.Pane Tawny.BendR
variable {C:ℝ}{c:Side}{n l d m r k p q w i N:ℕ}{U:BudgetPoint}
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas PCAC Patria Patria.Depth Patria.Rolls PCAC.Oren QCD.Grass.Ward Plans.Stamp.Stair
variable {S:Scheme}{R:Side}(A:Massive.Run S N R 6)(hA:A.Actual)(hi:i≤ N)
local notation "M"=> S.side R i
variable (a b:Flavor 6) (s t:Axis)(g:su.Color)(u:Averaging)(T:TaperHol)(Z:BudgetPoint)(D D1:ℝ)
local notation "φ"=> A.density i
local notation "G"=> marque (i:=i) A true a (0:Axis)
local notation "X"=> report A G u i 0
local notation "F"=> ms (i:=i) a A
local notation "Y"=> report A F u i 0
local notation "V"=> wave (gamma 0)
local notation "W"=> wave (gamma 1)
open QCD.Entr.Goals Patria.Gall.Seals
local notation "P"=>rayC φ a
local notation "B"=> touch (su.colorMat Gpick)
local notation "j"=> aux1
local notation "j'"=> aux2
local notation "B0"=> Zinc.whirl Gpick (gamma 1)
local notation "pB"=> (B0 j j')⁻¹
noncomputable def gain2 :ℝ:= ‖pB‖*‖entryH j j'‖*‖B‖
lemma gain_nn:0≤gain2:=by unfold gain2; positivity
local notation "L₀"=> Rod M T.T 1 P
local notation "λV"=> (Gall.helm M)⁻¹*(slope M 1 0 0-slope M 0 0 0)
local notation "C2"=> foil φ
local notation "vR"=> river2 (c:=M) 0 1
lemma σΦ (x:Bundle)(η:ℝ)(hx:‖x-W‖≤η): ‖pB*(x*B) j j'- 1‖ ≤ gain2 * η:=by
        have hp:B0 j j'≠0:= Plans.Stamp.Stair.trad.choose_spec.choose_spec -- lexical
        have ht: pB*(W*B) j j'=1:=by rw [show W*B= B0 from ?_]; exact inv_mul_cancel₀ hp; exact (Zinc.walk ..).symm
        let L':Bundle→L[ℂ]ℂ:= entryH j j'; rw[show pB * (x*B) j j'-1=pB* L' ((x-W)*B) from (by rw[sub_mul,map_sub,mul_sub]; change _= _- pB * (W*B) j j'; rw[ht]; rfl),norm_mul]; apply (mul_le_mul_of_nonneg_left (L'.le_opNorm _) (norm_nonneg _)).trans; apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (norm_mul_le ..) (norm_nonneg _)) (norm_nonneg _)).trans; unfold gain2; unfold L'; apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hx (norm_nonneg _)) (norm_nonneg _)) (norm_nonneg _)); exact le_of_eq (by ring)
-- Probe read Φ.River scaled.Drift. No StrongX Cost here. λ in selection chosen after κ.
include hA hi
variable (x:RawVec 10)(η:ℝ)(κ E:TaperHol) -- scrap
omit hA hi
local notation "O2"=> oracle2 (t:=1) -- n?
-- generic agencies
structure WealthR (T:TaperHol)(Z:BudgetPoint)(K Q:ℝ):Prop where
    k_nn : 0 ≤ K
    q_nn : 0 ≤ Q
    phase : ∀ c:Side,∀ (F':Density c 6)(n:ℕ)(aP:ℝ), Allow Z Gpick F' n aP →∀ a i j₁, ‖oracle2 1 0 1 a i j₁ Gpick F'- reed a a i j₁ (ballast (0:Multi 10) 0 T.T) (tent Gpick F' (Gall.glaze (indexT 1)))‖ ≤ (tick c+(c.val:ℝ)⁻¹)*K*aP
    spirit :∀ c:Side,∀ (F' P':Density c 6)(n:ℕ)(D:ℝ)(X':Label 10), Allow Z Gpick (foil P' F') n D→SungP (foil P' F')→Tally T 0 X' P' F'→10 ≤ n →∀ p i j₁, ‖river2 0 1 p i j₁ Gpick (foil P' F')-awake2 0 1 p i j₁ Gpick X'‖≤ (c.val:ℝ)⁻¹*Q*D
lemma dueT(hZ: 3 ≤ Z.power):∃ K Q:ℝ, WealthR T Z K Q:=by
       obtain ⟨K,hK,h⟩:= purseT 0 1 Gpick T Z (by omega); obtain ⟨Q,hQ,hP⟩:= speedT T Gpick 0 1 Z hZ (by decide) Tawny.KeysP.ruby_pick.choose_spec; exact ⟨K,Q,hK,hQ,h,hP⟩
variable (K Q:ℝ)(hP:WealthR T Z K Q)
variable (n1:ℕ)(hx:Tally T 0 (x.val 0) (A.density i) (report A (marque (i:=i) A true a 0) u i 0))
noncomputable def eW :ℝ:= ∑ i:Fiber, ‖V j i‖
lemma eW_nn:0≤ eW:=Finset.sum_nonneg fun i hi=>norm_nonneg _
-- accuracy costs scale(log window). state explicit
noncomputable def Élong (T:Side)(c1 c2 K Q η:ℝ)(z:ℂ):ℝ:= ‖z‖*(gain2*η)+‖z-1‖ + (‖pB‖ * ((T.val:ℝ)⁻¹*Q*c1) + ‖pB‖*‖z‖*(eW*((tick T+(T.val:ℝ)⁻¹)*K*c2)))
include hA hi hP hx
local notation "T2"=> awake2 0 1
lemma applause (hη:‖Rod M T.T 0 P-V‖ ≤η)(h:Globe.Tempo P)(hX:Allow Z Gpick (C2 X) n D)(hY:Allow Z Gpick (C2 Y) n D1)(hn:10 ≤ n):
       ‖pay2 (lookQ x) - Pi.single a 1‖ ≤ Élong M D D1 K Q η λV:=by
       let z:= λV; let C' := ((M).val:ℝ)⁻¹*Q*D; let E1:= (tick M+((M).val:ℝ)⁻¹)*K*D1
       have h0:0≤η:= (norm_nonneg _).trans hη
       have hC':0≤C':=by unfold C'; have hv:= hP.q_nn; have hh:0≤D:=(peaks_g ..).trans (hX.heatL a j j'); positivity
       have he: 0 ≤ E1:=by unfold E1; have hv:= hP.k_nn; have ht:= tick_g M; have he:0≤ D1:=(peaks_g ..).trans (hY.heatL a j j'); positivity
       have hE: 0 ≤ Élong M D D1 K Q η z:=by change 0 ≤ _ * (gain2*η)+‖z-1‖+(_ * C'+_*_*(eW*E1)); positivity[gain_nn,eW_nn]
       have hg:SungP (C2 X):= treated _ _ (dSung A hA hi) (by rw[arrivesHere]; exact inkS A hA _ 0 hi)
       apply (pi_norm_le_iff_of_nonneg hE).mpr; intro b; change ‖pB * T2 b j j' Gpick ((x.val) 0) - (Pi.single a 1: Flavor 6→ℂ) b‖≤_
       have hc: river2 0 1 b j j' Gpick (C2 X)= if b=a then z*(∑ i:Fiber,V j i*oracle2 1 0 1 b i j' Gpick (C2 Y)) else 0:=weight1 A hA hi a b 0 1 Gpick u j j' (show 1≤n from by omega) hx.unit hX.alive hY.alive (by decide)
       let R:=T2 b j j' Gpick ((x.val) 0); have hv:‖river2 0 1 b j j' Gpick (C2 X)- T2 b j j' Gpick ((x.val) 0)‖≤ C':= hP.spirit _ _ _ _ _ _ hX hg hx hn b j j'
       by_cases hb:b=a; swap
       · rw[hc,if_neg hb, zero_sub,norm_neg] at hv -- need rw hc
         rw [Pi.single_eq_of_ne hb,sub_zero,norm_mul]; apply (mul_le_mul_of_nonneg_left hv (norm_nonneg _)).trans; change _≤ ‖z‖*(gain2*η)+‖z-1‖+(‖pB‖*C'+ _*(eW*E1)); have hG:=gain_nn; have hE:=eW_nn; apply le_trans (le_add_of_nonneg_right (?_ : (0:ℝ) ≤ ‖pB‖*‖z‖*(eW*E1))); apply le_add_of_nonneg_left; all_goals positivity
       subst b; let v:= L₀; let k':= (∑ i:Fiber,V j i* oracle2 1 0 1 a i j' Gpick (C2 Y)); let x':= awake2 0 1 a j j' Gpick ((x.val) 0)
       have ht : ‖k'-(v*B) j j'‖≤ eW*E1:=by
             rw[show v* B= V*(V*v*B) from ?_, Matrix.mul_apply]; swap
             · rw[mul_assoc V v B,← mul_assoc V V, wave_mul,gamma_sq,wave_one,one_mul] -- edit
             unfold k'; rw [←sum_sub_distrib]; apply (norm_sum_le ..).trans; unfold eW; rw [sum_mul]; apply sum_le_sum; intro i' _; rw[← mul_sub,norm_mul]; refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _); have he:=hP.phase _ _ _ _ hY a i' j'; rw [read_t A hA hi a 1 Gpick u i' j' T (show 1 ≤ n from by omega) hx.unit.self_of_nhds hY.alive] at he; exact he
       let α:= pB * ((v*B) j j'); have hy: ‖α-1‖≤ gain2 *η:=σΦ v η (Oriole.lit P 0 1 T.T h η hη); have hy': ‖z*α-1‖≤ ‖z‖*(gain2*η)+ ‖z-1‖:=by rw [show z*α-1=z*(α-1)+(z-1) from (by ring)]; apply (norm_add_le ..).trans; rw [norm_mul]; gcongr
       rw [hc,if_pos rfl] at hv; have hh:‖pB*(x'-z*k')‖ ≤ ‖pB‖*C':=by rw [norm_mul]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); rw[norm_sub_rev]; exact hv
       have hg: ‖pB*z*(k' - (v*B) j j')‖ ≤ ‖pB‖*‖z‖*(eW*E1):=by rw [norm_mul,norm_mul]; exact mul_le_mul_of_nonneg_left ht (mul_nonneg (norm_nonneg _) (norm_nonneg _))
       rw [Pi.single_eq_same]; change ‖pB*x'-1‖≤ _; rw [show pB*x'-1 = z*α-1+(pB*(x'-z*k')+pB*z*(k'-(v*B) j j')) from (by unfold α; ring)]; exact (norm_add_le ..).trans (add_le_add hy' ((norm_add_le ..).trans (add_le_add hh hg)))
end YM.Massive.Patria.Gall.Cahoots
#print axioms YM.Massive.Patria.Gall.Cahoots.applause
#print axioms YM.Massive.Patria.Gall.Cahoots.dueT
