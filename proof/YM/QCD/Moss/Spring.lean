import YM.QCD.Pant.Inlet
import YM.QCD.Fold.Cafe
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Coset
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
variable (u:Fleet K I N) (v:Fleet K' J N)(z:EvenA C N →ₐ[ℝ] EvenA c N)
local notation "B"=>radiusB τ
-- protocol(LowWord) not restrict nonzero. X independent when instantiated from raw G/Y. p,p' must share ℕ exponent prices? ht p for Mint equality. no need phase real.
variable (hC he)
structure Page (hC:C.val=c.val*D)(he:2≤c.val)(u:Fleet K I N)(v:Fleet K' J N)(Z:EvenA C N →ₐ[ℝ] EvenA c N) (w:Pipe.Clump (stepped M H) J)(r:Pipe.Clump (stepped M h) I)(x:Site C)(n:ℕ) where
 goals : R'.path= R.path
 fees : R'.beta=R.beta
 size : R'.p= R.p
 mana : w.toRight ≃ r.toRight -- subtype coerces?
 memo (i:↥w.toRight):u.window (mana i).val = (v.window i.val).image ((Lace.project (h:=h) (H:=H) hC he).low.cut)
 late (i:↥w.toRight)(U: Grid f)(V:Grid c):Z (v.works i.val ((Lace.project (h:=h) (H:=H) hC he).high.links U) ((Lace.project (h:=h) (H:=H) hC he).low.links V))=u.works (mana i).val U V
 song : Finset (Music C F)
 news :w.toLeft=hatch (stepped M H) song
 cash : r.toLeft=hatch (stepped M h) (wrappers (Lace.project (h:=h) (H:=H) hC he) song)
 ink : ∀ i∈song,Mint.verse R'.path i≤ radiusB τ
 rate : Set.InjOn (verse_down (Lace.project (h:=h) (H:=H) hC he)) song
 reaches : v.fullA w⊆ neighbors n x
variable {hC he} {w:Pipe.Clump (stepped M H) J}{r:Pipe.Clump (stepped M h) I}{x:Site C}{n:ℕ}
variable (V:Page hC he u v z w r x n) {E:Tree.Forest (stepped M h).ratio}{G:Tree.Forest (stepped M H).ratio}
variable (hu:u.Famous)(hv:v.Famous) (hN: 2*(2*n+3)<c.val)
variable {A:Coat T E}{A':Coat T' G}
lemma pay_for (a:ℝ)(b:EvenA C N): z (a • b)= a • z b:=map_smul z.toLinearMap a b
include V hv hN
lemma petals (k:Air f su)(H':Stellar hC he P τ A A') (j:↥w.toRight): z (v.coming j.val A' (blow (Lx) k))= u.coming (V.mana j).val A k:=by
    let p:= (v.window j.val)
    have hf:p⊆neighbors n x:= ((halo_subset (30*radiusB τ) _).trans (hv.boot j.val)).trans (((v.suitcase G).leP w j.2).trans V.reaches)
    unfold Fleet.coming Fleet.riseP; rw [pay_for z,V.fees,H'.rolls, V.memo,H'.porter p n (by omega) x hf]
    apply congr_arg; rw [(H'.glassU ..).2.2,H'.views]; exact V.late .. -- H'.views rw inside nested expression? rw A'? H'.views only.
lemma height (k:Air f su)(H':Stellar hC he P τ A A') (p q:Finset ℕ): z ((v.suitcase G).capacityP w p A' (blow (Lx) k))=(u.suitcase E).capacityP r q A k:=by
   unfold capacityP; rw [pay_for z]; refine congr_arg₂ (· • ·) ?_ ?_
   · unfold Coat.term; rw [V.news,V.cash]; unfold Mint.hatch; rw [prod_map,prod_map]; unfold wrappers; rw [prod_image V.rate]
     exact prod_congr rfl fun i hi=> H'.granted V.goals V.size V.fees _ _ _ i (V.ink i hi) .. -- sig
   change z (∏ i∈w.toRight,v.coming i A' (blow (Lx) k))=∏ i∈r.toRight,u.coming i A k; rw [← prod_coe_sort w.toRight, ← prod_coe_sort r.toRight,map_prod]
   exact (prod_congr rfl fun i _=> petals u v z V hv hN k H' i).trans (Equiv.prod_comp V.mana (fun i=> u.coming i.val A k))
end YM.QCD.Moss
