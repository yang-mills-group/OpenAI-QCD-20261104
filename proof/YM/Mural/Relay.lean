import YM.Mural.Fil
import YM.Mural.Clan
/-! # Matrice transformation through the hard-limb mergers. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.PaletteT
open QCD QCD.Grass QCD.Creek Cupola QCD.Cove QCD.Sway QCD.Sway.OrbitG Function Finset Filter MeasureTheory NormedSpace
open Plate Stitch Tablet Ribbon Lattice Wilson Lat RG
open scoped BigOperators Topology Classical ContDiff
variable {D E F I:Type} [Fintype I]{c f:Side} (N:ℕ)(p:Unit→Site c) (t:ℝ)
local notation "M"=> ample N Unit
open Kites QCD.Finch Ruby Patron
noncomputable def pathsV (F: Patron.Rail c (ample N Unit) E)(f:E→Grid c→EvenA c (ample N Unit)): Patron.Rail c (ample N Unit) E:= ⟨F.addr,f⟩
variable (Y:Patron.Rail c (ample N Unit) E)(R:Option I→ E→Grid c→EvenA c (ample N Unit))(q:Unit→Bool)(Z:Support c)(g:Lat.Frame c)(K:Delta I)
structure Parade :Prop where
 style: ∀ j U,Dealers N p t q (fun i=> R i j U)
 verse: ∀ j U,Binds K (actC (ample N Unit) g) (fun i=>R i j (gauge g U)) (fun i=>R i j U)
 region: ∀ j U,¬ Z⊆ (Y.addr j).place →∀ i,Mint N p t q ∅ (R i j U)
variable (Q:Ruby.Hue c N D) (a b r:ℝ)
local notation "Q'"=> radial Unit Q
local notation "P!"=> pursue N p a Y t r
local notation "P0" i=> pathsV N Y (R i)
local notation "Pr" i=> pursue N p a (pathsV N Y (R i)) t r
variable (H:Parade N p t Y R q Z g K) (hv:0<a)(ht:0<t)(hp:straight K)(hx:∀ i,shadeG (Q.mean i))
-- alignment exact, without reducing dependent rail shape while summing weights.
noncomputable def portH (Q:Ruby.Hue c (ample N Unit) D)(i:Option I) (t:ℝ): Plot Q Y→Grid c→EvenA c M:= fun j U=> Ruby.payer Q (pathsV N Y (R i)) t U j.val
variable (Zs:Ruby.Hue c (ample N Unit) D)(hW:∀ j V i, Mint N p t q ∅ (Ruby.flower Zs (pathsV N Y (R i)) V (Sum.inr j)))
variable (hI:∀ j V,Binds K (actC (ample N Unit) g) (fun i=>Ruby.flower Zs (pathsV N Y (R i)) (gauge g V) (.inr j)) (fun i=> Ruby.flower Zs (pathsV N Y (R i)) V (Sum.inr j)))
include hW hI H ht hp
set_option maxRecDepth 2600 in
set_option maxHeartbeats 560000 in
lemma fruit : Parade N p t (Trail Zs Y b) (fun i=> portH N Y R Zs i b) q Z g K:=by
      let Pk i:=pathsV N Y (R i); let π j V i:=Ruby.flower Zs (Pk i) V j
      have hi j V : Dealers N p t q (π j V):=by
        rcases j with j|j; exact H.style j _
        exact fresh_tariff N p t _ (hW j V (none:Option I)) ht
      let F:=Dealers.clan (P:=I) (N:=N) (p:=p) (t:=t) (q:=q); let T:=actC M g
      have hj j V : Binds K T (π j (gauge g V)) (π j V):=by
         rcases j with j|j; exact H.verse j V; exact hI j V
      let cost (v:Grid c) (j:Plot Zs Y):= RG.flags b v∩ scopeK Zs Y j.val=badgeK Y j.val; let Yp i:=portH N Y R Zs i b
      let z j V i:= if cost V j then ∏ k∈j.val,π k V i else 0; have hm(i:Option I)(j:Plot Zs Y) (U:Grid c): Yp i j U=z j U i:=by
           unfold z cost Yp portH Ruby.payer; have he(s: Cart D E): badgeK (Pk i) s=badgeK Y s:=by unfold badgeK oriD; rfl
           have hf(k:Cart D E):scopeK Zs (Pk i) k=scopeK Zs Y k:=by unfold scopeK footD Ruby.home; rfl
           rw [show badgeK (pathsV N Y (R i)) j.val=_ from he _,show scopeK Zs _ j.val=_ from hf _]


      refine ⟨fun i V=>?_,fun i V=>?_,fun i V hQ j=>?_⟩
      · change Dealers _ _ _ _ (fun k=> Yp k i V); simp_rw [hm]; unfold z; split; · exact gatheredX F _ i.val (fun j _=>hi j V) (Dealers.unit I) (fun i hi j hj=>Dealers.combine hi hj)
        exact F.zero_mem
      · change Binds K T (fun i'=> Yp i' i (gauge g V)) (fun i'=>Yp i' i V); simp_rw [show ∀ i' U,Yp i' i U=z i U i' from fun i' U=> hm i' i U]; -- RHS still Y' expanded change
        unfold z cost; rw [gauge_flags]; split; swap; · exact unity _ _ hp 0 0 (map_zero _)
        next Hq=> exact binds_prod K T F (Dealers.unit I) (fun i hi j hj=>Dealers.combine hi hj) (fun u hu v hv i j=> Dealers.blouse (show Dealers N p t q u from hu) hv i j) (fun j=> π j (gauge g V)) (fun j=>π j V) _ (fun j _=> hi j V) (fun j _=> hj j V) hp
      change Mint _ _ _ _ _ (Yp j i V); rw [hm]; unfold z; split; swap; · exact Mint.none _
      apply (pocket N p t q ht).prod_mem; rintro (k|k) hh; swap; · exact hW _ _ _
      exact H.region k V (fun hx=> hQ (hx.trans (show (Y.addr k).place ⊆ scopeK Zs Y i.val from subset_biUnion_of_mem (footD Zs Y) hh))) j
omit hW hI H ht hp
noncomputable def pulseV (i:Option I) : Plot (radial Unit Q) (pursue N p a Y t r)→Grid c→EvenA c M:= portH N (pursue N p a Y t r) (fun i=>(pursue N p a (pathsV N Y (R i)) t r).warp) (radial Unit Q) i b
#check fruit
include H hv ht hp hx
lemma fiscal0 : Parade N p a (pursue N p a Y t r) (fun i=>(pursue N p a (pathsV N Y (R i)) t r).warp) q Z g K:=by
    constructor
    · exact fun j V=> renew N p t r a _ (H.style j V) hv
    · exact fun j V=> spinRev N p t g K r a _ _ (H.style j _) (H.verse j V) ht
    intro j V he i; exact emptyChange N p t r a _ (H.region j V he i) hv
omit H hv ht hp hx
include H ht hp hx
set_option maxHeartbeats 500000 in
-- `Trail` crumb. No price retag
lemma onward : Parade N p t (Trail (radial Unit Q) Y b) (fun i=> portH N Y R (radial Unit Q) i b) q Z g K:=by
   apply fruit N p t Y R q Z g K b H ht hp Q'
   · intro j V i; let y:=(Q').mean j V; let A:= pocket N p t q ht; have h:y∈A:=kindle N p t ht _; exact A.sub_mem (Loom.Fleet.exp_memD A _ h) A.one_mem
   intro j V; let T:= actC M g
   refine unity K T hp (exp ((Q').mean j (gauge g V))-1) (exp ((Q').mean j V)-1) (?_); rw [map_sub,map_one,map_exp]; · exact congr_arg (fun y:EvenA c M=> exp y-1) (Subtype.ext (paySector (I:=Unit) (Q.mean j) (hx j) V g))
   exact T.toLinearMap.toContinuousLinearMap.continuous
include hv
lemma advanceR : Parade N p a (limb N p a t r Q Y b) (pulseV N p t Y R Q a b r) q Z g K:= by
   exact onward N p a (pursue N p a Y t r) _ q Z g K Q b (fiscal0 N p t Y R q Z g K Q a r H hv ht hp hx) hv hp hx
omit H hv ht hp hx
end YM.MassiveQCD.PaletteT
#print axioms YM.MassiveQCD.PaletteT.fiscal0
#print axioms YM.MassiveQCD.PaletteT.fruit

#print axioms YM.MassiveQCD.PaletteT.advanceR
