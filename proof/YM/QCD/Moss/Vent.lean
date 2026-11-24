import YM.QCD.Moss.Coda
/-! # Transparent local filament. Prototype word for an exact period comparison. Forest, corrected slide choices and seam socks. No-limit letters. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Moss
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory ProbabilityTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Coat Animals
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets Horticulture
open Mixed Reserves Trees Beam Beam.Pipe Cove Leaf Lat Loom Loom.Fleet
open PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt PhysicalNext.Repeat.Deck
open Further.PhysicalPeriodLimitF933 Macrame Stellar Mint
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f C F L:Side} {P : Teller su}{O:Patch}{D :ℕ}{M:KernelChoices}
variable {h:f.val=c.val*O.L.val}{H:F.val=C.val*O.L.val}{hC:C.val=c.val*D}{he:2≤c.val}
local notation "Lx"=> Lace.project (h:=h) (H:=H) hC he
variable {W κ κ' μ β τ:ℝ} {R:Rep su f}{R':Rep su F}{X:ConnectedActivityE6.Target su P}{o:ConnectedActivityE6.Target.Order su W}
local notation "S"=>stepped M h
local notation "Y"=>stepped M H
variable {T:Tube su (stepped M h)} {T':Tube su (stepped M H)} {N:ℕ}{I J:Type}
variable {K:Cash W τ μ L X o κ T R}{K':Cash W τ μ L X o κ' T' R'}
variable (hC he)
open Loom Gas GasP Ursell Kit Fork
abbrev calm (L': Lace h H D) : DarkV C F→ DarkV c f:= Sum.map (Sum.map L'.high.cut L'.low.cut) L'.low.cut
def staid (L':Lace h H D) : PeaceV C F→PeaceV c f:= Sum.map (verse_down L') (calm L')
def spritz (L':Lace h H D) (p:BloomV C F):BloomV c f:= p.image (staid L')
def lesson (L':Lace h H D)(i:Wreath C F):Wreath c f:=⟨i.1,spritz L' ∘ i.2⟩
set_option quotPrecheck false
local notation "g"=> (Lx).high.cut
local notation "s"=> (Lx).low.cut
local notation "Y'"=>(Y).ratio
local notation "S'"=>(S).ratio
include hC he
lemma preen (X:Support F): (X.image (g)).image (S').parent=(X.image (Y').parent).image s:= by rw [image_image,image_image]; exact congr_arg (fun k:Site F→ Site c=>X.image k) (funext fun i=> Lace.position (Lx) i)
lemma intact (X:Support C) : Port.rig S' (X.image s)=(Port.rig Y' X).image g:=by
  have hf:(X.image (s)).image (S').embed=(X.image (Y').embed).image g:=by rw [image_image,image_image]; exact congr_arg (fun k:Site C→ Site f=>X.image k) (funext fun i=> ((Lx).stake i).symm)
  unfold Port.rig; rw [hf]; exact Deck.ringed (fineP h H hC) _ _
lemma diap (n:ℕ)(U:Support C): halo n (U.image (s))=(halo n U).image (s):= Deck.ringed hC U n
lemma bounce (n:ℕ) (i:DarkV C F): wades (S) n (calm (Lx) i)=(wades (Y) n i).image (s):=by
   rcases i with (i|i)|i
   · change halo _ ((trunkFt ((g) i) n).image (S').parent)=(halo _ ((trunkFt i n).image (Y').parent)).image _; rw [show trunkFt ((g) i) n=(trunkFt i n).image (g) from Deck.inclined (fineP h H hC) n i,preen,diap] -- args
   · change halo _ ((trunkFt ((S').embed ((s) i)) n).image (S').parent)=(halo _ ((trunkFt ((Y').embed i) n).image (Y').parent)).image (s)
     rw [← show (g) ((Y').embed i)=(S').embed ((s) i) from (Lx).stake i,show trunkFt ((g) ((Y').embed i)) n=(trunkFt ((Y').embed i) n).image g from Deck.inclined (fineP h H hC) n ((Y').embed i)] -- RHS Map splitter minor
     rw [preen,diap]
   change halo _ (trunkFt ((s) i) n ∪ (Port.rig S' _).image _)= (halo _ (trunkFt i n ∪ (Port.rig Y' _).image _)).image _; change halo _ (trunkFt ((s) i) n ∪ (Port.rig S' (trunkFt ((s) i) n)).image (S').parent)= (halo _ (trunkFt i n ∪ (Port.rig Y' (trunkFt i n)).image (Y').parent)).image _; rw [show trunkFt ((s) i) n=(trunkFt i n).image s from Deck.inclined hC n i,intact,preen,← image_union,diap]
lemma capital : Nest (Deck.divides hC) (staid (Lx)) (heartP (Y)) (heartP (S)) := by
   have hj:= onfloor (h:=h) (H:=H) hC he; exact (Stellar.nest_mint (Q:=M) (h:=h) (H:=H) (hC:=hC) (he:=he)).sum (((Deck.footing (h:=h) (H:=H) hC he).sum hj).sum hj)
variable (hp:R'.path= R.path)
include hp K K'
lemma modestM (i:PeaceV C F):gradeV R'.path i=gradeV R.path (staid (Lx) i) ∧ estateP K (staid (Lx) i)=(estateP K' i).image s:=by
   rcases i with i|i
   · exact Meadow.contempt hC he (I:=K) (I':=K') hp i
   refine ⟨rfl,?_⟩; change halo _ (wades (S) _ (calm (Lx) i))=(halo _ (wades (Y) _ i)).image _; rw [bounce,diap]
lemma charging (i:BloomV C F): floorV K (spritz (Lx) i)=(floorV K' i).image s:=by
    unfold floorV spritz
    rw [image_biUnion]; have he p:estateP K (staid (Lx) p)= _ :=(modestM hC he hp p (K:=K) (K':=K')).2; ext y; simp only [mem_biUnion,he,mem_image]; grind
lemma orderR (p:BloomV C F) (hr:Set.InjOn (staid (Lx)) p)(hk:Set.InjOn (s) (floorV K' p)):Fiat K (spritz (Lx) p) ↔ Fiat K' p :=by
   have heq:= card_image_of_injOn hr
   have hh : Ac.Spark (estateP K') p↔Ac.Spark (estateP K) (spritz (Lx) p):= by convert! Meadow.preheated _ _ _ _ _ (fun i=>(modestM hC he hp (K:=K) (K':=K') i).2) hr hk using 2
   have hv i:gradeV R'.path i= _:=(modestM hC he hp (K:=K) (K':=K') i).1
   constructor
   · intro h; exact ⟨hh.2 h.hot,heq ▸ h.sizes,fun i hi=> hv i ▸ h.earn _ (mem_image_of_mem _ hi)⟩
   intro h; refine ⟨hh.1 h.hot,heq ▸ h.sizes,fun i hi=>?_⟩
   obtain ⟨i,hi,rfl⟩:=mem_image.mp hi; exact hv i ▸ h.earn _ (by assumption)
end YM.QCD.Moss
