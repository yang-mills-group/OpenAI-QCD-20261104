import YM.Pollen.Attune
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
open Cape
local notation "Q"=> domeE o V H d s F paid
variable (X:Grid c)(J:Finset I)(hz:Spaced o J U.B)(hC :1<U.B*U.B)
local notation "q'"=> shutter Z J
include hs hz hC
lemma enumeratedU (i:D): q' ((Ω X) s (F.mark i X))=q' (F.mark i X)+ ∑ j:↥(matings o s F i), q' ((W).mark ⟨i,j⟩ X):=by
     let z:= s.toFinset.powerset; rw [paysU _ _ d s hs,map_sum]; let Px:=F.mark i X; let u(v: Finset I):= q' ((Φ X) (gΦ v) Px); let L:= matings o s F i; change ∑ j∈ z,u j=q' Px+∑ j:↥L,u j.val; rw [← add_sum_erase z u (show ∅∈z from (by simp [z])),sum_coe_sort,show u ∅= q' Px from ?_]; swap; · unfold u; rw [show List.filter (fun j=>decide (j∈(∅:Finset I))) s=[] from by simp]; rfl
     apply congr_arg; symm; refine sum_subset (show L⊆ z.erase ∅ from (fun j hj=> mem_erase.mpr ⟨(memo o s F (⟨i,j,hj⟩:E)).2.2.1.ne_empty,mem_powerset.mpr (memo o s F (⟨i,j,hj⟩:E)).1⟩)) fun j hv hr=>?_
     obtain ⟨hd',hp'⟩:=mem_erase.mp hv; have hh:= mem_powerset.mp hp'; let l:= gΦ j; have hL:l.toFinset=j:=viewingP _ _ hh; by_cases hz': j⊆ J; swap
     · exact shutU o V H d l X J Px (fun he=>hz' (hL ▸ he))
     by_cases hx : j⊆ barn o (Y i); swap
     · obtain ⟨k,hk,he⟩:=Finset.not_subset.mp hx; have hK:= vanishedU o V H d l X Px (Y i) (h.costume ..).2 (by rw[hL]; exact fun i hi j hj he=>hz i (hz' hi) j (hz' hj) he) hC (hs.filter _) (List.mem_toFinset.mp (hL.symm ▸ hk)) (fun hp=>he ((inside ..).2 hp)); exact (congr_arg (q') hK).trans (map_zero _)
     exact (congr_arg (q') (spectralU o V H d l X (F.z i) Px (h.costume ..).1 (fun hp=>hr (mem_filter.mpr ⟨mem_powerset.mpr (subset_inter hh hx), nonempty_iff_ne_empty.mpr hd', hL ▸ hp⟩)))).trans (map_zero _)
local notation "t_"=>U.threshold
local notation "B!" i:arg=> oldMask paid (Y i) t_ (F.mark i) X
local notation "T'"=> Cape.vesta o Q t
local notation "H'"=> withdraw 6 o t
include hp
lemma eraM (i:D): q' ((Ω X) s (B! i))=q' (B! i)+ ∑ j:↥(matings o s F i), (q' ((W).mist t_ (⟨i,j⟩:E) X)+ q' (H' ((T').mean (⟨i,j⟩:E) X))):=by
     let L:= matings o s F i; have hz (j:↥L): q' ((W).mist t_ (⟨i,j⟩:E) X)+q' (H' ((T').mean (⟨i,j⟩:E) X))= q' (oldMask paid (Y i) t_ ((W).mark (⟨i,j⟩:E)) X):=by
          rw [show H' _=_ from (show H' ((T').mean (⟨i,j⟩:E) X)=(Q).wick _ X from Cupola.home _ _ _ hp _),←map_add]; apply congr_arg; change _ + (oldMask _ _ _ _ _- Reel.mist (W) t_ _ _) = _; abel
     rw [sum_congr (s₁:=Finset.univ) rfl (fun j _=>hz j)]; unfold oldMask; split
     · exact enumeratedU o V H d s F f g h hs X J ‹Spaced ..› hC i
     by_cases hV:Healthy t_ (Y i) X; · rw[masked_eq _ _ _ _ hV]; simp_rw [masked_eq _ _ _ _ hV]; exact enumeratedU o V H d s F f g h hs X J ‹Spaced ..› hC i
     simp_rw [masked_ne _ _ _ _ hV,map_zero,sum_const_zero,add_zero]
include he hK he0 hx hc hd hA hW hΦ
-- stamp cooperation
variable (hpT:1 ≤ t)(hP:paid=true→∀ i X,Stitch.Tablet.credits t (F.mark i X) ≤ g i)
include hpT hP
lemma canopyU (hv: Summable (fun i=>B! i)) : q' ((Ω X) s (∑' i,B! i))= q' ((∑' i,B! i)+(W).rope t_ X+H' (swarm T' X)):=by
     let f i:= (B! i); let Tq(i:E):=q' ((W).mist t_ i X); let AS:= (q').comp H'; let g'(i:E):= AS ((T').mean i X); let F':=(W).rope t_ X; let q₀:=(q').toLinearMap.toContinuousLinearMap; let qv:= ((q').comp ((Ω X) s)).toLinearMap.toContinuousLinearMap; let Qu:=∑' i,B! i; have hh:= mossy o V H d s F ‹D→Site c› g h hs hc hx hp hd Ft ε ζ C he hK he0 hA hW hΦ -- ‹D→Site c› uses `f` shadow? Lean
     have hxV:= tip o X (W) _ hh hA hpT; have hθ:Summable (fun i:E=> (T').mean i X):=((wearsA o V H d s F ‹D→Site c› g h hs hc hx hp hd Ft ε ζ C he hK he0 hA hW hΦ paid hP).heated hpT hA X).1 -- order
     have hb:HasSum Tq (q' F'):=q₀.hasSum (show HasSum _ F' from hxV.hasSum); have hB:HasSum g' (q' (H' (swarm T' X))):=(AS).toLinearMap.toContinuousLinearMap.hasSum hθ.hasSum
     rw [map_add,map_add (q') Qu,show q' _= _ from (hb.tsum_eq).symm,show q' _= _ from hB.tsum_eq.symm] -- selects which? ambiguity
     have hf:Summable fun (i:E)=>Tq i+g' i:=hb.summable.add hB.summable; rw [add_assoc, ← hb.summable.tsum_add hB.summable]; rw[hf.tsum_sigma]; let F0 i:=q' (B! i); have hy:HasSum F0 (q' Qu):=q₀.hasSum hv.hasSum; have hΩ := qv.hasSum hv.hasSum; refine hΩ.tsum_eq.symm.trans ?_; rw [← show (∑' i,F0 i)=_ from hy.tsum_eq,←hy.summable.tsum_add hf.sigma]; refine tsum_congr fun i=>?_ ; have hp:= eraM o V H d s F ‹D→Site c› g h hs ‹0<t› paid X J hz hC i; rw [tsum_fintype]; exact hp
end YM.MassiveQCD.Sample.Basal
#print axioms YM.MassiveQCD.Sample.Basal.canopyU
