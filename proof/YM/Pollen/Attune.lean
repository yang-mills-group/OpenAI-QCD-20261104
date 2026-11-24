import YM.Pollen.Glow
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
local notation "U'"=> mRent U.B U.power U.order ε
local notation "V'"=>mCash U.B U.power U.order Ft ε b (a*x)
local notation "X₀"=>a*x*2^U.order
local notation "φp"=> Real.exp (b+ε)
variable (hΦ:hullP U.B Ft*(Real.exp (b+ε)*(a*x*2^U.order))≤ ε)
-- input eval policy BEFORE mask
variable (paid:Bool)
noncomputable def oldMask (paid: Bool)(Y₀:Support c)(u:ℝ) (x:Grid c→ P): Grid c→ P:=if paid then x else masked u Y₀ x
open Cape
noncomputable def domeE : Lure c 6 I (E):= ⟨fun i=> (V! i),fun i V=> oldMask paid (Y i.fst) U.threshold ((W).mark i) V-masked U.threshold (V! i) ((W).mark i) V,(W).z⟩ -- macro V notation Hygiene
local notation "Q"=> domeE o V H d s F paid
local notation "l'" i:arg=> (Y i.fst)
-- X' bigger. UsesFinal proving old mask reads on larger.
omit h
lemma maskK (v w: S)(H:v⊆w)(g:Grid c→P)(hg:LocalOn w g): UsesFinal U.threshold w (oldMask paid v U.threshold g):=by
    intro U1 U2 hv hh; unfold oldMask; split; · exact hg U1 U2 hv
    have hk:Healthy U.threshold v U1 ↔ Healthy U.threshold v U2:=by
         apply iff_of_eq; apply propext; simp only [Healthy,Finset.disjoint_iff_inter_eq_empty]; have he (X:Grid c) : v∩flags U.threshold X=v∩(w∩ flags U.threshold X):=(by rw[← Finset.inter_assoc,inter_eq_left.mpr H]); rw[he,hh,← he]
    by_cases hp:Healthy U.threshold v U1; · rw [masked_eq _ _ _ _ hp,masked_eq _ _ _ _ (hk.mp hp)]; exact hg U1 U2 hv
    rw [masked_ne _ _ _ _ hp,masked_ne _ _ _ _ (fun hv=>hp (hk.2 hv))]
include h
lemma relents : Lure.On o q Q U.threshold:=by
     have hB:=awardedU o V H d s F f g h
     refine ⟨fun i U1 U2 hu hv=> congr_arg₂ (·-·) (maskK o V H paid (Y i.fst) _ (show (Y i.fst) ⊆ V! i from subset_union_left) _ (hB.room i) _ _ hu hv) (Cape.MaskR _ _ (hB.room i) U1 U2 hu hv),fun i=> ?_,fun i X hx hp=> ?_,fun i X=> ?_,fun i X g=> ?_,hB.stamp,hB.stays⟩ -- MaskR ns
     · have hm:Measurable (oldMask paid (Y i.fst) U.threshold ((W).mark i)):=by unfold oldMask; split; exact hB.permit i; exact masked_measurable _ _ _ (hB.permit i)
       exact hm.sub (masked_measurable _ _ _ (hB.permit i))
     · apply hx; change oldMask paid (Y i.fst) U.threshold ((W).mark i) X-Reel.mist (W) U.threshold i X=0; rw[show Reel.mist (W) _ i X= _ from masked_eq U.threshold (V! i) _ X hp]; unfold oldMask; split; exact sub_self _; rw [masked_eq _ _ _ _ (hp.mono_left (show (Y i.fst) ⊆ V! i from subset_union_left)),sub_self]
     · change Stitch.lights _ _ _ _ (oldMask _ _ _ _ X-Reel.mist (W) U.threshold i X); rw [sub_eq_add_neg]; let Y':=(V! i); have hl: Stitch.lights ((W).z i) Y' o q (oldMask paid (Y i.fst) U.threshold ((W).mark i) X):=by
           unfold oldMask; split; · exact hB.stage i X
           by_cases hh:Healthy U.threshold (Y i.fst) X; · rw[masked_eq _ _ _ _ hh]; exact hB.stage i X
           rw [masked_ne _ _ _ _ hh]; exact ⟨polite_nil ..,clad.nil _⟩
       have hk:=Cape.upM o q (W) hB (t:=U.threshold) i X; exact ⟨hl.1.lays hk.1.minus, hl.2.plus hk.2.neg⟩
     change parcelColor 6 g I (oldMask _ _ _ _ _-masked U.threshold (V! i) _ _)=oldMask paid _ _ _ _-masked U.threshold (V! i) _ _; rw [map_sub]; have ht (Yw:S): parcelColor 6 g I (masked U.threshold Yw ((W).mark i) (Lattice.gauge g X))= masked U.threshold Yw ((W).mark i) X:=by
            have hk: Healthy U.threshold Yw (Lattice.gauge g X) ↔ Healthy U.threshold Yw X:=by simp [Healthy]
            by_cases hp:Healthy U.threshold Yw X; · rw [masked_eq _ _ _ _ (hk.2 hp),masked_eq _ _ _ _ hp]; exact hB.tint ..
            rw[masked_ne _ _ _ _ (fun h=>hp (hk.1 h)), masked_ne _ _ _ _ hp, map_zero]
     refine congr_arg₂ (·-·) ?_ (ht _); unfold oldMask; split; exact hB.tint ..; exact ht _
local notation "λ'"=> Cape.vesta o Q t
include hΦ he0 hA hW he hK hs hc hx hp hd
lemma wearsA (hBP: paid=true→∀ i X,T t (F.mark i X) ≤ g i) : Wax λ' U.threshold U.B b (V'*C) t:=by
     have hb:= relents o V H d s F f g h paid; refine ⟨vespers _ _ _ hb,(fun i=> φ' i),innerBill o V H d s F f g h hs hc hx hp hd Ft ε ζ C he hK he0 hA hW hΦ,fun i X=>?_⟩; rw [show ‖token c _ t ((λ').mean i X)‖ = T t ((Q).wick i X) from from_full o hp _]; let Y':=(V! i); have hh (Z':P)(hz:Z'=0): T t Z'≤ φ' i:=by rw [hz,Stitch.Tablet.credits,map_zero,Cove.load_zero]; exact (billsA o V H d s F f g h hs hc hx hp hd _ _ ((W).addr i).anchor).travels
     by_cases hV:Healthy U.threshold Y' X; · exact hh _ (by_contra fun hv=> hb.expense _ X hv hV)
     change T t (oldMask _ (Y i.1) _ _ X- masked U.threshold Y' _ X)≤_; rw [masked_ne _ _ _ _ hV,sub_zero]; unfold oldMask; split; next hv=> exact worthU o V H d s F f g h hs hc hx hp hd i X (hBP hv _ _)
     by_cases hu':Healthy U.threshold (Y i.1) X; swap; · exact hh _ (masked_ne _ _ _ _ hu')
     rw [masked_eq _ _ _ _ hu']; exact worthU o V H d s F f g h hs hc hx hp hd _ _ (by simpa only [leftDerivs,one_pow,mul_one] using (firstStep o F f g h i.1 X hu' hp).paid [] (Nat.zero_le _) (by simp))
end YM.MassiveQCD.Sample.Basal
#print axioms YM.MassiveQCD.Sample.Basal.wearsA
