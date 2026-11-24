import YM.QCD.Stem.Lotus
import YM.QCD.Grove.Rodeo
/-! # Transfers and tacks for Atlas on all folds. Not for Ribbon terms. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Moss
open QCD Lat PhysicalNext.Repeat
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {c f C F L₀ : Side} {P : Patch} {M D' n: ℕ} {K : Teller su}
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q: KernelChoices} {hC:C.val=c.val*M} {he:2  ≤  c.val} {p a b W U V t d r : ℝ}
open Loom Fleet Patron Cove GasP Grove Stew
local notation "B'"=> radiusB p
section spread
variable {I:Type}{N w:ℕ}{G:Gem c N I}{X:Finset I}{J:BudgetPoint}
lemma aura (g:I→ℝ)(hx:∀ i∈X,Woven (G.addr i).site (G.addr i).support J t (G.view i) (g i))(hp:Ac.Hit (fun i=>(G.addr i).support) w g r d)(hr:0≤r): Pockets X G J t d:=by
    refine ⟨g,hx,fun x=>?_⟩; let Y:=pondC X G x; let f i:= if x∈(G.addr i).support then g i * Real.exp (r*coverNumber w (G.addr i).support) else 0
    have h := hp x; have hf i := h.1 i; refine le_trans (b:=∑ i∈Y,f i) (sum_le_sum ?_) ((h.2.1.sum_le_tsum Y (fun i _=> hf i)).trans h.2.2)
    intro k hk; have hh:= mem_filter.mp hk; unfold f; rw [if_pos hh.2]; exact le_mul_of_one_le_right (hx k hh.1).travel (Real.one_le_exp (by positivity)) -- inspect
end spread
section one
variable {S:StepData c f}{R:RG.Rep su f}{T:Tube su S} {X: ConnectedActivityE6.Target su K} {o:ConnectedActivityE6.Target.Order su W}{D: Cash W p a L₀ X o U T R}{I:Type}{N:ℕ}{B:Fleet D I N}{Y:Bouquet D B}{A:Clusters B.Bright→RegularAddress c}{V₀:Chi}{B₀:BudgetPoint}
local notation "T₀"=>crude B V₀ A
lemma chromate (hv:Peace B)(he:∀ i,(A i).support=seatP B.lightF i) (hz:Pockets (dashX n Y) (T₀) B₀ t d) : SoilB (dashX n Y) (T₀) B₀ (tideP X.halo B') t:=by
    have ht: Dyed (T₀):= upstream B A V₀ hv
    refine ⟨fun i hi=>⟨_,hz.tokenEq.choose_spec.1 i hi⟩,fun i hi x hx=> ?_,fun i _=> ht.gauge i,fun i _ V=>ht.num i V,fun i _=> ht.real i⟩
    obtain ⟨i,hh,hv,rfl⟩:= (oceanM ..).1 hi; have hg :(A (Y.heightV i hh)).support=_:= (he _).trans (Y.shower i hh)
    rw [show ((T₀).addr (Y.heightV i hh)).support=_ from hg] at *
    exact palace D hh x hx
end one
local notation "L" => Lace.project (h:=h) (H:=H) hC he
variable {N:ℕ}{T:Tube su (stepped Q h)}{T':Tube su (stepped Q H)} {X: ConnectedActivityE6.Target su K} {o:ConnectedActivityE6.Target.Order su W}
   {R:RG.Rep su f}{R':RG.Rep su F}{D: Cash W p a L₀ X o U T R} {D₀: Cash W p a L₀ X o V T' R'}
variable {I J:Type}{B:Fleet D I N}{Z:Fleet D₀ J N}{Y:Bouquet D B}{Y':Bouquet D₀ Z}
local notation "A₀"=> tideP X.halo (radiusB p)
variable {g:Site C→ℂ}{χ:Chi}{E: BudgetPoint}{A:Clusters B.Bright→RegularAddress c}{A':Clusters Z.Bright→RegularAddress C}
local notation "V₁"=>crude B χ A
local notation "H₁"=>dashX n Y
local notation "V₂"=>crude Z χ A'
local notation "H₂"=>dashX n Y'
variable (hv: B.Famous)(hh:Peace B)(hA:∀ i,(A i).support=seatP B.lightF i)
  (hyp:Z.Famous)(hu:Peace Z)(hE:∀ i,(A' i).support=seatP Z.lightF i)
  (hp:Alive hC he B Z (Folding.axes (Lace.project (h:=h) (H:=H) hC he).low g N) Y Y')
include hA
lemma perks (x:Site c): ∃ v:(↥(seatX D x n)≃ ↥(pondC (H₁) (V₁) x)),∀ i:↥(seatX D x n),(v i).val=Y.heightV i.val ((leads ..).1 (mem_filter.mp i.2).1).1 :=by
    let Q':=seatX D x n; let R':=pondC (H₁) (V₁) x; let f (i:↥Q'):= Y.heightV i.val ((leads ..).1 (mem_filter.mp i.2).1).1
    have hf i:f i∈ R':=by
      have ht:=mem_filter.mp (i.2); refine mem_filter.mpr ⟨(oceanM ..).2 ⟨i.val,_,((leads ..).1 ht.1).2,rfl⟩,?_⟩
      rw [show ((V₁).addr (f i)).support=summitV D i.val from (hA _).trans (Y.shower ..)]; exact ht.2
    let h (i:↥Q'):↥R':=⟨_,hf i⟩
    refine ⟨Equiv.ofBijective h ⟨fun i j h=> ?_,?_⟩,fun i=> rfl⟩
    · apply Subtype.ext; have he:f i=f j:=congr_arg Subtype.val h; unfold f at he; exact congr_arg (fun x:{z// Mossy D z}=> x.val) (Y.warranty (a₁:=⟨_,((leads ..).1 (mem_filter.mp i.2).1).1⟩) (a₂:=⟨_,((leads ..).1 (mem_filter.mp j.2).1).1⟩) he) -- param x
    intro i; obtain ⟨hx,hp'⟩:=mem_filter.mp (show i.val ∈pondC _ _ _ from (i.2)); obtain ⟨j,hk,hv,hx⟩:= (oceanM ..).1 hx; have hu' : x∈summitV D j:=by rw [← Y.shower j hk,hx,← hA]; exact hp'
    let j':↥Q':=⟨j,mem_filter.mpr ⟨(leads ..).mpr ⟨hk,hv⟩,hu'⟩⟩; exact ⟨j',Subtype.ext (show (h j').val=i.val from hx)⟩
include hv hh hyp hu hE hp
lemma harpoon (hr:E.threshold=Pressure.temp p) (hC':2*(2*A₀+3)<c.val)(hz: Pockets (H₁) (V₁) E t d)(hd:Pockets (H₂) (V₂) E t b): LiftQ (L).low (V₁) (V₂) (H₁) (H₂) g E A₀:=by
    refine officer _ _ _ _ _ _ E A₀ (chromate hh hA hz) (chromate hu hE hd) (fun i=> Meadow.garden hC i (by omega)) fun x=>?_
    obtain ⟨v,hv'⟩:= perks (Y:=Y') (χ:=χ) (n:=n) hE x; obtain ⟨u,hu'⟩:= perks (Y:=Y) (χ:=χ) (n:=n) hA ((L).low.cut x); obtain ⟨s,hs⟩:= fibers g hp x n hC' -- explicit k? check implicit
    refine ⟨u.symm.trans (s.symm.trans v),?_⟩; intro i; obtain ⟨i,rfl⟩:=u.surjective i; obtain ⟨i,rfl⟩:=s.surjective i; simp only [Equiv.trans_apply,Equiv.symm_apply_apply]; rw [hu',hv']
    have hx:= mem_filter.mp (i.2); let p':=i.val
    have h₀: Mossy D (s i).val:= ((leads ..).1 (mem_filter.mp (s i).property).1).1
    have h₁: Mossy D₀ i.val:= ((leads ..).1 hx.1).1
    constructor
    · rw [show ((V₁).addr (Y.heightV (s i).val h₀)).support=summitV D (s i).val from (hA _).trans (Y.shower ..),show ((V₂).addr (Y'.heightV i.val h₁)).support= _ from (hE _).trans (Y'.shower ..), hs]; exact pitchRoll hC he hp.birth _
    intro W hw; rw [hr] at hw
    have hy: flags (Pressure.temp p) ((L).low.links W)=∅:=by ext z; rw [show z∈flags (Pressure.temp p) ((L).low.links W) ↔ _ from flagged hC W z (show _ from (by have h:=D.laws.data.room.buys; omega)) (Pressure.temp p),hw]; simp
    let V:=Folding.axes (L).low g N; let m j (h:Mossy D j):=Y.heightV j h; let q:=lesson (L) i.val
    have hQ : Mossy D q:=(congr_arg (Mossy D) (hs i)).mp h₀
    have hm:m (s i).val h₀=m q hQ:=by simp [m,hs,q]
    have hp U (he: flags (Pressure.temp p) U=∅) j:(V₁).view j U=B.honest χ U j:= (masked_eq (Pressure.temp p) (A j).support ((V₁).view j) U (show _ from (by unfold Healthy; rw [he]; simp))).symm.trans (literalX B A χ hA hv hh j U)
    let Q':= Y'.heightV i.val h₁; have hg: (V₂).view Q' ((L).low.links W)= Z.honest χ ((L).low.links W) Q':= (masked_eq (Pressure.temp p) (A' Q').support ((V₂).view Q') _ (by unfold Healthy; rw [hy]; simp)).symm.trans (literalX Z A' χ hE hyp hu Q' _)
    change V ((V₂).view Q' _)= (V₁).view (m _ _) _; rw [hp W hw,hg,hm]; exact offersV B Z V hv hyp Y Y' ‹_› _ x h₁ hQ W hw hx.2 hC' χ -- order
end YM.QCD.Moss
