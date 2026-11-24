import YM.Profiles.Hoards
import YM.Profiles.Wreaths
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon Apron Apron.Grove Cupola Plate Card Iris
open MassiveQCD.Sample.LoomT Massive.Poised Massive.Poised.Plans Massive.Poised.Plans.Stamp Massive.UV Stative Massive.Poised.Pipes
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical Stamp
variable {I J E D' :Type}[Fintype I][Fintype J]
open QCD.Kites QCD.Conductor QCD.Acre QCD.Acre.Rails QCD.Struck QCD.Struck.Library Weft
variable {c f L:Side}{v t Θ Γ α β κ:ℝ}{P:BudgetPoint}{k n l m d j:ℕ}
namespace Posy
open NormedSpace Stew Ruby Quills -- h.OK
variable {U:Type}(Y:Reel c 6 I E)(F:Film c 6 I J)(K: Patron.Rail c 6 U)(p:I→Bool)(o:I→Site c)
local notation "A"=> Keys c 6
local notation "B"=> Spine I
variable (W:Grid c)
lemma lightCost (x: EvenA c 6): ‖rootR (Spine I) (Keys c 6) x‖=‖x‖:= by exact scenic Embedding.inl x.val -- note changed V.Uv.H Norm.P.Panel.
lemma scrapeP (x: Patio (A⊕B)) (s:Finset B): ‖pluck A s x‖ ≤ ‖x‖:=by
   change ‖scrape A s _‖ ≤ ‖(x.val)‖; rw [Grass.norm_def,Grass.norm_def]; simp_rw [Ribbon.bank]; let e:=fun i:Finset A=>i.disjSum s; change (∑ i:Finset A,‖Grass.coef (e i) x.val‖) ≤ _; rw [← sum_image (f:=fun j=> ‖Grass.coef j x.val‖) (s:=Finset.univ) (show Set.InjOn e _ from fun i _ j _ h=>by exact Eq.trans ((toLeft_disjSum ..).symm) ((congr_arg Finset.toLeft h).trans (toLeft_disjSum ..)))]; exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _=> norm_nonneg _)
lemma provision (h: Y.Occupant o p v P 2 α t (fun _=>1))(hv:1≤ v)(hα:0 ≤ α): ‖Reel.rope Y P.threshold W‖ ≤ (Fintype.card (Site c):ℝ)*t:=by
    obtain ⟨u,hF,hX⟩:=h.reserve; simp only [abs_one, prod_const_one,one_mul] at hF
    let F i:=Y.mist P.threshold i W; have hp(i): ‖F i‖ ≤ u i:=by
         obtain ⟨j,hj⟩:= h.booked.stays i; have hx:=hX i j hj
         by_cases ht: Healthy P.threshold (Y.addr i).support W; swap; · unfold F Reel.mist; rw [masked_ne _ _ _ _ ht,norm_zero]; exact hx.travels
         unfold F Reel.mist; rw [masked_eq _ _ _ _ ht]
         apply le_trans (loaded (Y.mark i W).val (Stitch.Tablet.chip v A B) (fun j=>by rcases j with j|j; exact hv; exact le_rfl)); change Stitch.Tablet.credits v (Y.mark i W) ≤ u i; rw [show Stitch.Tablet.credits _ _= _ from Stitch.Tablet.polite_bill _ _ (h.booked.stage i W|>.1) (zero_lt_one.trans_le hv)]; let φ:= Reel.speaker p Y i; apply le_trans (viewer (o j) (φ W) 2 (zero_lt_one.trans_le hv)); exact hx.pole W ht [] (by simp) (fun _ h=>by simp at h)
    have hh := QCD.Acre.Rails.spiritual u _ hF (fun i=> ⟨_,(Y.addr i).anchor⟩) hα (fun i=>(norm_nonneg _).trans (hp i)); let g:=budget_mono hh (fun i=> norm_nonneg _) hp; exact (norm_tsum_le_tsum_norm g.2.1).trans g.2.2 -- namespace? see.
-- don't want J Fintype. separate Vb.
variable {Z E₀:Type}{Dg Vg T δ:ℝ}
variable (F: Film c 6 I Z)(K':Patron.Rail c 6 E₀)
lemma filmP (hV:Kites.Quits K' k t β v κ)(hk:F.Stock 6 k δ α κ Γ (fun _=>1))(hF:F.Beat 6 o p T)(hg:1 ≤ β)(hγ:1 ≤ δ)(hv:0≤v)(hα:0≤α)(ht:1 ≤ κ) : ‖Film.reports 6 F K' T W‖ ≤ Real.exp ((Fintype.card (Site c):ℝ)*(t+Γ)):=by
    obtain ⟨u,hu,hX⟩:=hV.cost; let U i:= K'.warp i W; obtain ⟨g,hZ,hQ⟩:=hk.price; have hp(i):0≤u i:=(norm_nonneg _).trans (hX i 1); have h₁(i): ‖U i‖≤ GasP.taxed (Ruby.oriD K') u β i:= ((Loom.tore (U i) ht).trans (hX i W)).trans (le_mul_of_one_le_left (hp i) (one_le_pow₀ hg)); let F' i:= F.mark i W
    have h₂(i:Z): ‖F' i‖ ≤ Film.fares 6 F g (fun _=>1) δ i:=by
         have hw : ‖F' i‖ ≤ g i:= (loaded (F.mark i W).val (Stitch.Tablet.chip κ A B) (fun j=>by rcases j with j|j; exact ht; exact le_rfl)).trans (hZ i W); unfold Film.fares taxed; simp only [abs_one, prod_const_one,one_mul]; exact hw.trans (le_mul_of_one_le_left ((norm_nonneg _).trans hw) (one_le_pow₀ hγ))
    let r':=rootR B A; have hw(i): ‖r' (U i)‖ ≤ GasP.taxed (Ruby.oriD K') u β i:=(lightCost _).trans_le (h₁ i)
    have hx:= QCD.Acre.Rails.spiritual _ _ hu (fun i=>(K'.addr i).alive.mono (K'.addr i).part) hv (fun i=>(norm_nonneg _).trans (hw i)); have hy:= QCD.Acre.Rails.spiritual _ _ hQ (fun i=>(F.addr i).alive.mono (F.addr i).part) hα (fun i=> (norm_nonneg _).trans (h₂ i))
    let z i:= Film.spruced 6 F K' i W; have hm: SumBudget (fun i=> ‖z i‖) ( (Fintype.card (Site c):ℝ)*(t+Γ)):=by rw [mul_add]; exact Extra.Iteration.Cost.sum (budget_mono hx (fun i=>norm_nonneg (r' (U i))) hw) (budget_mono hy (fun i=>norm_nonneg (F' i)) h₂)
    let P i:=Plate.roof (Film.addressSets 6 F K') z (RG.flags T W) i; have hc(i):‖P i‖≤ ∏ j∈i, ‖z j‖:=by
        unfold P Plate.roof; split; exact Finset.norm_prod_le ..; rw [norm_zero]; exact prod_nonneg fun i _=>norm_nonneg _
    have hf:= budget_mono (QCD.Acre.Rails.sunpow hm) (fun i=> norm_nonneg _) hc; exact (norm_tsum_le_tsum_norm hf.2.1).trans hf.2.2
lemma exp_price (x: Patio (A⊕B)): ‖NormedSpace.exp x‖ ≤ Real.exp ‖x‖:=by
    -- Mathlib exp_bound. or cove stipend
    let Y:= A⊕B; let p:= fun i:Y=>(1:ℝ); have he(w:Patio Y) : Creek.load p (light _ w)=‖w‖:=by rw [dry _ (show ∀ i,0<p i from fun _=>zero_lt_one)]; change _=‖w.val‖; rw [Grass.norm_def]; unfold p; simp
    have ht:‖NormedSpace.exp x-1‖ ≤ Real.exp ‖x‖ -1:= (he _).symm.trans_le (Cove.bought p x ‖x‖ (he x|>.le)); linarith only [(norm_sub_norm_le ..).trans ht,norm_one (α:= Patio Y)]
end Posy
end YM.MassiveQCD.Sample
#print axioms YM.MassiveQCD.Sample.Posy.filmP
