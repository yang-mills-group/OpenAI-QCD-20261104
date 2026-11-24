import YM.Pollen.Story
import YM.Clays.Benny
import YM.Clays.Acer
import YM.Bister.Body
import YM.Pollen.Oak
import YM.Helio.Ribbons
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample.Basal
open QCD QCD.Grass QCD.Cove Lattice Finset Ribbon Cupola Stew
open Function Lattice Wilson Creek Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Plate Plate.Card Relight Ruby Massive.PCAC
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k:ℕ}{I D:Type}[Fintype I]{a t b w x v θ m:ℝ}
variable (o:I→Site c) {U:BudgetPoint}
variable (V: I→Grid c→ Fields c N→L[ℂ]Fields c N) (H:∀ i,Suit (o i) U a (V i)) (d:I→ℂ) (s:List I)
local notation "P"=> Patio (Keys c N⊕Spine I)
local notation "S"=>Support c
local notation "q"=> traceI I
set_option quotPrecheck false
open Pressure QCD QCD.Kites QCD.Jets QCD.Jets.Touch QCD.High Push Push.AbsoluteSums Trees ConnectedActivityE6
variable (L:Side)(z:ℝ)(Ft:ℕ)
local notation "T"=> taxK L z
local notation "ε"=> (1/512:ℝ)
local notation "A!"=> (1+81*Real.exp ε)
local notation "ρ"=> A!*(taxK L z (1/20))⁻¹
local notation "b!"=> highR L z
structure BakeD (L:Side)(z:ℝ):Prop where
    leg : StackK (highR L z) (taxK L z (39/20)) (taxK L z (37/20)) (21/256) (18/256) (22/256) 1
    rush : degreePrice (highR L z) ((1+81*Real.exp (1/512))*(taxK L z (1/20))⁻¹) (2/256) ≤ 1/2
    pores : ((1+81*Real.exp (1/512))*(taxK L z (1/20))⁻¹)*(1-1/2)⁻¹ ≤1
    side :1 < highR L z*highR L z
lemma bakeAble :∀ᶠ t:ℝ in atTop,BakeD L t:=by
    let g x:ℝ:=16*(1+(highR L x:ℝ))^4; let k x:=A!*(taxK L x (1/20))⁻¹; have hk:Rate su L (-1) k:= (couplings L (by norm_num)).mul_left A!; have hg:Rate su L 0 g:=(radH L).mul_left 16; let e:=(2/256:ℝ)
    filter_upwards [Sail.pulseBottle L (37/20) (39/20) (18/256) (3/256) (by norm_num) (by norm_num) (by norm_num) (by norm_num),((hg.mul hk |>.mul_right e⁻¹).mul_left 4).below (by norm_num) (1/2) (by norm_num),(hk.mul_right ((1-1/2:ℝ)⁻¹)).below (by norm_num) 1 zero_lt_one,(Work.E01.radiusB_tendsto.comp (Work.E09.betaF_growth su L)).eventually_ge_atTop 2] with x hx hv hh hB
    rw [show (18/256:ℝ)+3/256=21/256 by norm_num,show (21/256:ℝ)+1/256=22/256 by norm_num] at hx
    refine ⟨hx,?_,(le_abs_self _).trans hh, Nat.lt_of_lt_of_le (show 1<(2:ℕ)*2 from (by norm_num)) (Nat.mul_le_mul hB hB)⟩
    have hp: 0 < k x:=by unfold k taxK; positivity
    have hm : (Animals.ballCost (highR L x):ℝ) ≤ g x:=by unfold g Animals.ballCost; push_cast; have h0 := pow_le_pow_left₀ (show 0 ≤ (↑(highR L x):ℝ)+↑(highR L x)+1 by positivity) (show (↑(highR L x):ℝ)+↑(highR L x)+1≤2*(1+↑(highR L x)) by linarith) 4; linarith only [h0]
    show degreePrice _ (k x) e ≤ _; unfold degreePrice Trees.stretch; refine le_trans ?_ ((le_abs_self _).trans hv); rw[div_eq_mul_inv]; gcongr
variable (F:Patron.Rail c (ample N I) D)(h: Wage.Tip N o (traceI I) F U t (42/256) (taxK L z 2))
local notation "g'"=>furtherK o V H d s F t
local notation "G'"=>Stretch.Basin g' (roofV o s F) U.threshold
variable (hw:1 ≤ t)(hy:0 ≤ x)(hΦ:s.Nodup)(hv:∀ i, ‖d i‖ ≤ x) (ha:0≤a)(hF:Fires o Ft)
include H h hw hy hΦ hv ha hF
local notation "λ'"=> withdraw N o t
variable (hU:BakeD L z)(hB:U.B=highR L z)
local notation "v₀"=>(25/256:ℝ)
local notation "w'"=>(23/256:ℝ)
local notation "μ'"=>(21/256:ℝ)
variable (hE:hullP U.B Ft*(Real.exp (25/256+1/512)*(a*x*2^U.order))≤1/512)
include hU hB hE
-- per F=T
set_option quotPrecheck false
local notation "Xs" X:arg=> actU (fun k=> V k X) (fun k=> (H k).bean X) d
variable {J:Type} (Y':Patron.Rail c N J)
lemma earnsB (hz:Correspond (faultK N o t F) Y'): Wage.Tip N o q (G') U t μ' (T (39/20)) ∧ Correspond (faultK N o t (G')) Y'∧ ∀ (X:Grid c) (i:Finset I),Spaced o i U.B→ shutter (Keys c N) i ((Xs X) s (λ' (heartK F U.threshold X)))=shutter (Keys c N) i (λ' (heartK (G') U.threshold X)):=by
    let C:= T (1/20); have hh (i:ℝ) (h:0 ≤ i):1 ≤ T i:= Real.one_le_exp (mul_nonneg h (fan_pos ..).le); have hC:1 ≤ C:=hh _ (by norm_num); have hC0:=zero_lt_one.trans_le hC; have hZ:μ'+(2/256:ℝ) =w':=(by norm_num); have ht:=zero_lt_one.trans_le hw
    have hG:hullP U.B Ft * (Real.exp w' * (a*x)) ≤ ε:=by
           apply le_trans _ hE; apply mul_le_mul_of_nonneg_left _ (by unfold hullP; positivity); exact mul_le_mul (Real.exp_monotone (by norm_num)) (le_mul_of_one_le_right (mul_nonneg ha hy) (one_le_pow₀ (by norm_num))) (mul_nonneg ha hy) (Real.exp_pos _).le
    have hY:Quits g' U.B ρ (T (39/20)) (μ'+2/256) t:=by
           rw [hZ]; have h_ :C*T (39/20)= T 2:=by unfold C taxK; rw[← Real.exp_add]; congr 1; ring
           refine budgetK o V H d s F h ht hΦ C Ft hF (by norm_num : 0 < ε) (by norm_num) (by norm_num) ha hy hv hC (hh _ (by norm_num)) h_.le hG ?_
           have hp : beamFee U.B Ft (a*x) w' ε ≤ 81*Real.exp ε:=by
                 unfold beamFee; nlinarith only [mul_le_mul_of_nonneg_right hG (Real.exp_pos (1/512)|>.le)] -- ε normal
           change C⁻¹+ _ * C⁻¹ ≤ _ * C⁻¹; rw [add_mul,one_mul]; exact add_le_add_right (mul_le_mul_of_nonneg_right hp (inv_pos.mpr hC0).le) _
    exact audited o V H d s F h ht (hh _ (by norm_num)) hw (by norm_num) hΦ (hB.symm ▸ hU.side) Y' hz (hh _ (by norm_num)) hY (by norm_num) (by norm_num) (mul_pos (by positivity) (inv_pos.mpr hC0)) (hB.symm ▸ hU.rush) (by norm_num) hU.pores
end YM.MassiveQCD.Sample.Basal
#print axioms YM.MassiveQCD.Sample.Basal.bakeAble
#print axioms YM.MassiveQCD.Sample.Basal.earnsB
