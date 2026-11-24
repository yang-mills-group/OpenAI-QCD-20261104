import YM.QCD.Moss.Slip
/-!
 # Music park lift at marked width. Includes inverse addressing, so no multiplicative
 weight guessing when κ duplicated.
 -/
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
variable {c f C F L₀ : Side} {P : Patch} {M D' : ℕ} {K : Teller su}
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q: KernelChoices} {hC:C.val=c.val*M} {he:2  ≤  c.val} {p a b W U V : ℝ}
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {T : Tube su (stepped Q h)} {T' : Tube su (stepped Q H)} {R:RG.Rep su f} {R':RG.Rep su F}
    {X : ConnectedActivityE6.Target su K} {o : ConnectedActivityE6.Target.Order su W}
    {I : Cash W p a L₀ X o U T R} {I' : Cash W p a L₀ X o V T' R'}
    (hC he)
local notation "B" => radiusB p
local notation "D" => tideP X.halo B
local notation "t" => Mint.width X.halo B B
variable (x : Site C)
variable (hp:R'.path= R.path)
include hp hC he I I'
local notation "τ"=>orbitD X.halo B
local notation "x'"=>Macrame.splitter (Deck.divides hC) x
lemma recollect (m:ℕ)(z: BloomV c f)(hz:Fiat I z)(hk: floorV I z⊆ neighbors D' (x'))(hr:D' + τ ≤ m)(hm:2*m < c.val): ∃ v, Fiat I' v∧ floorV I' v ⊆ neighbors m x ∧ spritz (L) v=z:=by
    let l:= L; let f:=staid l
    have hA:= capital (h:=h) (H:=H) (M:=Q) hC he
    choose α hα hα' using hA.esc x
    let v:=z.image α; have hh:spritz (L) v=z:=by unfold spritz v; rw [image_image,show staid (L) ∘ α=id from funext hα,image_id]
    have hi i (hi:i∈v): heartP (Y) i∈floorV I' v∧ estateP I' i⊆neighbors m x:=by
        obtain ⟨j,hj,rfl⟩:= mem_image.mp hi
        have ht:= modestM (K:=I) (K':=I') hC he hp (α j); have hs:= (ht.1.trans (congr_arg _ (hα j))).trans_le (hz.earn _ hj); have ha:= centersP I' (α j) hs
        have hd:separation x (heartP (Y) (α j)) ≤ D':=(hα' j).trans_le ((neighbors_mem ..).1 (hk (northG I hz j hj)))
        exact ⟨mem_biUnion.mpr ⟨_,hi,ha.1⟩,fun i hi=> (neighbors_mem ..).2 ((separation_triangle x (heartP (Y) (α j)) i).trans ((Nat.add_le_add hd ((neighbors_mem ..).1 (ha.2 hi))).trans hr))⟩
    have hx:floorV I' v ⊆ neighbors m x:=by intro i h; obtain ⟨j,hj,hx⟩:=mem_biUnion.mp h; exact (hi j hj).2 hx
    have hB : Set.InjOn (staid (L)) v:=fun i h j hg he=> hA.point hm x i j ((neighbors_mem ..).1 (hx (hi i h).1)) ((neighbors_mem ..).1 (hx (hi j hg).1)) he
    exact ⟨v,(orderR (K:=I) (K':=I') hC he hp v hB ((Meadow.garden hC x hm).mono (coe_subset.mpr hx))).1 (hh.symm ▸ hz),hx,hh⟩ -- K not notation check
lemma recap (v:Wreath c f)(hz:Mossy I v)(hp': (x')∈summitV I v)(hr: 2*(D+τ)<c.val) : ∃ u, Mossy I' u ∧ x∈summitV I' u ∧ lesson (L) u=v:=by
   choose α hα hg hf using fun i=> recollect hC he x hp (I':=I') _ (v.2 i) (hz.each i) (eachV (z:=v) i |>.trans (palace _ hz _ hp')) le_rfl hr
   let u: Wreath C F:=⟨v.1,α⟩
   have hs : lesson (L) u=v:= by unfold lesson u; congr 1; exact funext hf
   have ht:summitV I' u⊆ neighbors (D+τ) x:=by intro i hi; obtain ⟨j,hj,hi⟩:= mem_biUnion.mp hi; exact hg j (by assumption)
   have hy:= receipts (I:=I) hC he x hp u hr ht hα; rw [hs] at hy
   refine ⟨u,⟨hz.size,hα,hy.symm ▸ hz.moves⟩,?_,hs⟩
   obtain ⟨i,hk,hh⟩:=mem_image.mp (show (L).low.cut x∈(summitV I' u).image (L).low.cut from (by rw [← pitchRoll hC he hp (I:=I) (I':=I') u,hs]; exact hp'))
   exact ((Meadow.garden hC x hr) (ht hk) (show x ∈neighbors (D+τ) x from (neighbors_mem ..).2 (by simp)) hh :i=x) ▸ hk
end YM.QCD.Moss
