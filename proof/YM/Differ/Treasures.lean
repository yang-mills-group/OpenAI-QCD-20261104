import YM.Differ.View
import YM.Profiles.Uranus
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
namespace GreenCap.Pavilion
open Kites NormedSpace Stags Sample.Gel Sample.Gel.May Massive.Poised.Plans.Stamp
variable (q:I→Bool)(o:I→ Cover)(H:Massive.SourceRead.TaperHol){U:Source.Hol su}(B:Massive.Lining.Temper.Collage.Exhibit U)(l:I→Label d)(hp:∀ i,moored (l i).val (q i))
local notation "A"=> Keys c 6
local notation "X"=>Patio (A⊕Spine I)
set_option quotPrecheck false
local notation "ow"=>wrap c ∘ o
local notation "Ω"=> loc -- dummy
variable {ν δ ζ:ℝ}(n' j₀ k₀:ℕ) (V₀ B' t:ℝ)(p:BudgetPoint)(he:Pilot H B d p.order p.power n' j₀ k₀ ν δ)(hv:1 ≤ t)(hQ:30*(k₀+1) ≤ c.val)
namespace EntranceW
variable (E:I→Type)[hE:∀ i,Fintype (E i)] (F:∀ i:I,CentreFrame (c:=c) p v (l i) (q i) B (o i) (k₀+1) (E i) Empty)
local notation "G₁" i:arg=> F i
local notation "P₁" i:arg=> ritual (F i)
local notation "S"=> spineV
local notation "Π"=> hQ -- optional
-- weights input=v.Not same outer v! want fan via partial.Core instead abstract v. pert parser.Depends hQ. 
variable (Xc Vc:ℝ)(hX:∀ i, Published (F i) H n' j₀ (1/8) t Xc 0)(hV:∀ i,Courtesy B (o i) (l i) (q i) p (F i) 4 Vc)
variable (hv':1 ≤ v)
local notation "o†" i:arg =>fun (_:Unit)=> wrap c (o i)
local notation "Yf" i:arg => Puff.stool 6 (wrap c (o i)) (P₁ i) p v (fun _=>∅) (fun _=>1)
local notation "Zf" i:arg=> Stags.baptism 6 (ow) q v i (Yf i)
noncomputable def plume (i:I)(V:Grid c) :=∑ j:Jars d⊕ E i, Stags.amber (c:=c) 6 q i (((ritual (F i)).roll.mark j) V)
local notation "M'"=>plume q o B l k₀ p E F -- arg order
lemma wholeq (i:I)(V:Grid c): Polite q {i} (M' i V) ∧ Cove.light (A⊕Spine I) (M' i V)=stake A (burst q {i}) (S B (o i) (l i) (q i) p (F i) V):=by
    let Q:=P₁ i; let U j:= (Q.roll).mark j V; let W:= Spine I; have h(j:Jars d ⊕ E i) : _∧ _:= (show Polite q {i} (Stags.amber 6 q i (U j)) ∧ Cove.light (A⊕Spine I) (Stags.amber 6 q i (U j))=stake A (burst q {i}) (Q.fill j V) from ⟨(goldPay 6 q i (U j) (worthE _ _ _ (Q.beams j) V)).1,(goldMap 6 q i (U j) (worthE _ _ _ (Q.beams j) V)).trans (congr_arg _ (worthG _ _ _ (Q.beams j) V))⟩) -- `worthE` needs h.beam
    have hx : Cove.light (A⊕Spine I) (M' i V)=stake A (burst q {i}) (S B (o i) (l i) (q i) p (F i) V):=by unfold plume spineV; rw [map_sum,map_sum]; exact sum_congr rfl fun j _=> (h j).2
    exact ⟨⟨_,hx.symm⟩,hx⟩
include hV hX he hv' hQ
open QCD.Ruby Relight
lemma virtuous (i:I) : Wax (Zf i) p.threshold p.B 4 Vc v ∧ (∀ j, (ow i)∈ (Zf i).bud j) ∧ (∀ j, shadeG ((Zf i).mean j))∧∀ j V,Mint 6 (ow) v q {i} ((Zf i).mean j V):=by
    obtain ⟨f,hf,hp,hh⟩:= (hV i).paid
    have he':=(rendition he rfl rfl hv' hQ _ (hX i)).1 -- order
    obtain ⟨h1,h2,h3⟩:= Puff.paidSize 6 (wrap c (o i)) (P₁ i) p v (fun _=>∅) (fun i=>Finset.empty_subset _) (fun _=>1) he' f hf (fun i V _=>hp i V) (show Ac.Hit _ p.B _ 4 Vc from spend_collect _ _ (by simp only [norm_one,one_mul]; exact ⟨fun i=>mul_nonneg (hf i) (Real.exp_pos _).le,Summable.of_finite,(by rw [tsum_fintype]; exact hh)⟩)) (zero_lt_one.trans_le hv')
    have h0(j): (ow i)∈ (Yf i).bud j:= (show wrap c (o i)∈((P₁ i).addr j).support from (he'.anchor j) ▸ ((P₁ i).addr j).anchor); obtain ⟨hd,hp'⟩:= Stags.lustre (O:=p) 6 ow q v i (Yf i) h3 h1 h2 hv' h0; exact ⟨hd,h0,fun j=> (hp' j).1, fun i=>(hp' i).2⟩
omit hV hX he hQ
lemma toll (i:I)(V:Grid c): withdraw 6 (ow) v (swarm (Zf i) V)= M' i V- Stags.amber (c:=c) 6 q i (Reel.rope (P₁ i).roll p.threshold V):=by
   unfold swarm plume Reel.rope; rw [tsum_fintype,tsum_fintype,map_sum,map_sum,← sum_sub_distrib]
   refine sum_congr rfl fun j _=>?_
   let Φ:= banknote 6 (ow) v; let P:= (P₁ i)
   have hP : withdraw 6 (o† i) v ((Yf i).mean j V)=(P.roll).mark j V-Reel.mist P.roll p.threshold j V:=by
       -- `Puff roll.O.Mask.C`
       have hV:0<v:=zero_lt_one.trans_le hv'; change withdraw 6 (o† i) v ( (1:ℂ) • (masked _ ∅ _ V- masked _ _ _ V)) = _ -- supply
       rw [one_smul,map_sub, Puff.muting 6 _ P v _ _ _ _ hV, Puff.muting 6 _ P v _ _ _ _ hV,masked_eq _ _ _ V (Finset.disjoint_empty_left _)]; all_goals first| rfl| exact hV
   -- baptism
   let S' := amber (c:=c) 6 q i; have ht : withdraw 6 (ow) v ((Zf i).mean j V)=S' (withdraw 6 (o† i) v ((Yf i).mean j V)):=Cupola.home 6 _ _ (zero_lt_one.trans_le hv') _
   rw [ht,hP,map_sub]
end EntranceW
end GreenCap.Pavilion
end YM.MassiveQCD.Sample
#print axioms YM.MassiveQCD.Sample.GreenCap.Pavilion.EntranceW.virtuous
#print axioms YM.MassiveQCD.Sample.GreenCap.Pavilion.EntranceW.toll
