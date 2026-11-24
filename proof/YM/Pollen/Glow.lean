import YM.Pollen.Linda
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
variable {c:Side}{k:ℕ}{I D:Type}[Fintype I]{a t b w x v θ m:ℝ}
variable (o:I→Site c) {U:BudgetPoint}
variable (V: I→Grid c→ Fields c 6→L[ℂ]Fields c 6) (H:∀ i,Suit (o i) U a (V i)) (d:I→ℂ) (s:List I)
local notation "P"=> Patio (Keys c 6⊕Spine I)
local notation "S"=>Support c
local notation "q"=> traceI I
set_option quotPrecheck false
local notation "Φ" X:arg=> effU (fun k=> V k X) (fun k=> (H k).bean X) d
local notation "Ω" X:arg=> actU (fun k=> V k X) (fun k=> (H k).bean X) d
local notation "Z"=>Keys c 6
open ConnectedActivityE6 Blaze King
local notation "K"=> wag
local notation "T"=>Stitch.Tablet.credits
variable (F:Reel c 6 I D)(f:D→Site c)(g:D→ℝ)(h:ValidX o F f g U t)
-- occ.
local notation "E"=> Oper o s F
local notation "Y" i:arg=> (F.addr i).support
local notation "gΦ" i:arg=> s.filter (fun j=>j∈ (i:Finset I))
local notation "W"=>etherU o V H d s F
include H h
variable (hs:s.Nodup)(hc:0 ≤a) (hx:0 ≤ x)(hp:0<t)(hd:∀ i,‖d i‖ ≤x)
local notation "A"=> (a*x)
local notation "m'" i:arg=> mintA (a:=a) (U:=U) o s F g i x
local notation "V!" i:arg=> ((W).addr i).support
local notation "φ'" i:arg=>mE o V H d s F g i x
variable (Ft:ℕ)(ε ζ C:ℝ)(he:Ac.Hit (fun i:D=> (F.addr i).support) U.B g ζ C)(hK:Fires o Ft)(he0:0<ε)(hA:0 ≤ b)(hW:b+3*ε ≤ ζ)
open Reserves
noncomputable def mRent (B m k:ℕ)(ε:ℝ):ℝ:= let Q:=4+2*(m*k); (4*(B:ℝ)+2)^Q * polyPrice ε Q
noncomputable def mCash (B m k F:ℕ)(ε b A':ℝ):ℝ:=mRent B m k ε*beamFee B F (A'*2^k) (b+ε) ε
local notation "M"=> 4+2*(U.power*U.order)
local notation "U'"=> mRent U.B U.power U.order ε
local notation "V'"=>mCash U.B U.power U.order Ft ε b (a*x)
local notation "X₀"=>a*x*2^U.order
local notation "φp"=> Real.exp (b+ε)
variable (hΦ:hullP U.B Ft*(Real.exp (b+ε)*(a*x*2^U.order))≤ ε)
include hs hc hx hp hd hΦ he0 hA hW he hK
lemma innerBill: Ac.Hit (fun i:E=> V! i) U.B (fun i=>mE o V H d s F g i x) b (V' * C):=by
     have hh : b+ε+2*ε≤ ζ:=(by linarith only [hW]); let τ:= beamFee U.B Ft X₀ (b+ε) ε; have hy:0 ≤ X₀:=by positivity
     have hS:Ac.Hit (fun i:E=> V! i) U.B (fun i=>m' i) (b+ε) (τ*C):= woodPays o _ (matings o s F) (fun i j hj=> ⟨(memo o s F (⟨i,j,hj⟩:E)).2.2.1,(memo o s F (⟨i,j,hj⟩:E)).2.1⟩) U.B Ft U.B_pos (X₀) hy g (fun i=>(h.fee i).travels) he (add_nonneg hA he0.le) ε he0 hK hΦ hh
     intro i; rw [mCash,mul_assoc]; let Z':= U'; have hP:0≤ Z':=by dsimp only [Z',mRent, Reserves.polyPrice]; positivity
     refine budget_mono (budget_scale hP (hS i)) (fun j=>ite_nonneg (mul_nonneg (billsA o V H d s F f g h hs hc hx hp hd j _ ((W).addr j).anchor).travels (Real.exp_pos _).le) le_rfl) fun j=> ?_
     dsimp only; let z:=coverNumber U.B (V! j); let p:=(z:ℝ); split; next hv=>
            let R:=(4*(U.B:ℝ)+2)^M; let B:= 1+(wag (V! j) U.B:ℝ); have hB: B≤ (4*(U.B:ℝ)+2)*(1+p):=by unfold B wag p z; push_cast; nlinarith [Nat.cast_nonneg (α:=ℝ) U.B]
            have hh: B^M ≤ Z'*Real.exp (ε*p):=by
                apply le_trans (pow_le_pow_left₀ (by unfold B; positivity) hB M); rw [mul_pow]; exact (mul_le_mul_of_nonneg_left (polynomial_cost he0 (show 0 ≤ p from Nat.cast_nonneg _) M) (show 0 ≤ R by unfold R; positivity)).trans_eq (by unfold Z' mRent polyPrice; ring)
            have he:0 ≤ m' j:=mul_nonneg (pow_nonneg hy _) (h.fee _|>.travels); exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh he) (show 0 ≤ Real.exp (b*p) from (Real.exp_pos _).le)).trans_eq (by change Z'*Real.exp (ε*p)*(m' j)*Real.exp (b*p) = Z'*((m' j)*Real.exp ((b+ε)*p)); rw[add_mul,Real.exp_add]; ring)
     rw [mul_zero]
omit hΦ he0 hA hW he hK
lemma worthU (i:E)(X:Grid c) (hpΦ:T t (F.mark i.1 X)≤ g i.1): T t ((W).mark i X)≤ φ' i:=by
      let z:=gΦ i.snd.val; let x':= F.mark i.1 X; have hf:=spendsU o V H d z X x' hp hc hx hd; change T t ((W).mark i X) ≤ (A)^z.length * _ at hf; rw [show z.length= i.snd.val.card from payScope s hs i.snd.val (memo ..).1] at hf; have hy:0 ≤ A:=mul_nonneg hc hx
      refine hf.trans ((mul_le_mul (pow_le_pow_left₀ hy (le_mul_of_one_le_right hy (one_le_pow₀ (by norm_num:(1:ℝ)≤2))) _) hpΦ (load_nn ..) (pow_nonneg (show 0 ≤ a*x*2^U.order by positivity) _)).trans ?_); exact le_mul_of_one_le_left (show 0 ≤ m' i from (mul_nonneg (pow_nonneg (show 0 ≤ X₀ by positivity) _) (h.fee _|>.travels))) (one_le_pow₀ (by simp)) -- syntax
include hΦ he0 hA hW he hK
lemma mossy : (W).Occupant o q t U 2 b (V'*C) (fun _=>1):=by
     have hb:=awardedU o V H d s F f g h; have hi:=innerBill o V H d s F f g h hs hc hx hp hd Ft ε ζ C he hK he0 hA hW hΦ; refine ⟨hb,(fun i=>φ' i),?_, fun i j hj=>billsA o V H d s F f g h hs hc hx hp hd _ _ (hb.stamp i (mem_image_of_mem _ hj))⟩; simp only [abs_one,prod_const_one,one_mul]; exact hi
end YM.MassiveQCD.Sample.Basal
#print axioms YM.MassiveQCD.Sample.Basal.mossy
