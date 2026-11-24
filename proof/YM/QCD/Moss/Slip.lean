import YM.QCD.Moss.Vent
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
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q: KernelChoices} {hC:C.val=c.val*M} {he:2 ≤ c.val} {p a b W U V : ℝ}
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
lemma eachV {Jx:Cash W p a L₀ X o U T R} {z: Wreath c f}(i:Option (Fin z.fst)): floorV Jx (z.2 i)⊆summitV Jx z:= Finset.subset_biUnion_of_mem (floorV Jx ∘ z.2) (mem_univ _)
-- need both step types standalone so generalize above
include hC he
lemma genitive (hh : 2*D'<c.val) {v w: BloomV C F} (hz:∀ i∈v,separation x (heartP (Y) i)≤D') (ht:∀ i∈w,separation x (heartP (Y) i)≤D') (hp:spritz (L) v=spritz (L) w) : v=w:= by
  let L':=staid (L); have he:=capital (hC:=hC) (he:=he) (h:=h) (H:=H) (M:=Q); ext i; constructor
  · intro hi; obtain ⟨j,hj,hp⟩:= mem_image.mp (show L' i∈ spritz (L) w from hp ▸ (show L' i ∈ spritz (L) v from mem_image_of_mem L' hi)); exact (he.point hh x i j (hz i hi) (ht j hj) hp.symm).symm ▸ hj
  intro hi; obtain ⟨j,hj,hp⟩:=mem_image.mp (show L' i∈spritz (L) v from hp.symm ▸ (show L' i∈spritz (L) w from mem_image_of_mem L' hi)); exact (he.point hh x i j (ht i hi) (hz j hj) hp.symm).symm ▸ hj
omit hC he in
lemma engirds (v:Wreath C F) (hv:Mossy I' v) (hz:x∈summitV I' v) (i): floorV I' (v.2 i)⊆neighbors D x:= (eachV (Jx:=I') (z:=v) i).trans (palace _ hv x hz)
lemma inquire (v u: Wreath C F) (hv:Mossy I' v) (hu:Mossy I' u) (hx:x∈summitV I' v) (hk:x∈summitV I' u) (hC':2 * D < c.val) (h:lesson (L) u=lesson (L) v): u=v:= by
  have he : u.fst=v.fst:= congr_arg (fun i : Wreath c f=> i.fst) h; rcases v with ⟨n,v⟩; rcases u with ⟨m,u⟩; dsimp only at he; subst m
  unfold lesson at h; injection h with h hh; congr 1; funext i; let V:=v
  apply genitive (Q:=Q) hC (by assumption) x hC' _ _ (congr_fun hh i)
  · intro j hk'; exact (neighbors_mem ..).1 ((eachV (Jx:=I') (z:=⟨_,u⟩) i|>.trans (palace _ hu x hk)) (northG I' (hu.each i) j hk'))
  intro j hk; exact (neighbors_mem ..).1 ((eachV (Jx:=I') (z:=⟨_,v⟩) i|>.trans (palace _ hv x hx)) (northG I' (hv.each i) j hk))
lemma rings (v:Wreath C F) (hv:Mossy I' v) (hx:x∈ summitV I' v) (hp:2*D<c.val) (i) : Set.InjOn (staid (L)) (↑(v.2 i) : Set (PeaceV C F)):= by
  have hI:= engirds x v hv hx i
  intro y hy z hz he; exact (capital (M:=Q) (hC:=hC) (he:=by assumption) (h:=h) (H:=H)).point hp x y z ((neighbors_mem ..).1 (hI (northG I' (hv.each i) y hy))) ((neighbors_mem ..).1 ((eachV (Jx:=I') (z:=v) i).trans (palace _ hv x hx) (northG I' (hv.each i) z hz))) he
variable (hp : R'.path=R.path)
include hp I I'
lemma pitchRoll (z: Wreath C F) : summitV I (lesson (L) z)= (summitV I' z).image (L).low.cut:= by unfold summitV lesson; unfold unionOf; ext i; simp only [Function.comp_apply, mem_image,mem_biUnion,charging («K»:=I) (K':=I') hC he hp]; grind
lemma receipts (z:Wreath C F) (hZ:2*D'< c.val) (hz: summitV I' z⊆ neighbors D' x) (hu: ∀ i,Fiat I' (z.2 i)) :
    coefficient (blocked (floorV I')) z.2=coefficient (blocked (floorV I)) (lesson (L) z).2:= by
  apply Meadow.movement; intro i j; let f:=floorV I'; have hf i: f (z.2 i)⊆neighbors D' x := (eachV (Jx:=I') (z:=z) _).trans hz
  have hm i s (hh:s∈z.2 i):separation x (heartP Y s) ≤ D':= (neighbors_mem ..).1 (hf i (northG I' (hu i) s hh)); have hv i: ((floorV I ∘ (lesson (L) z).2) i)=(f (z.2 i)).image (L).low.cut:= charging hC he hp _
  have hy i : floorV I ((lesson (L) z).2 i)= (f (z.2 i)).image (L).low.cut:= hv i
  apply or_congr; · exact ⟨fun hx=>congr_arg (spritz (L)) hx,genitive hC he x hZ (hm i) (hm j)⟩
  unfold Ac.meets; rw [hy,hy]; constructor
  · rintro ⟨v,h,hx⟩; exact ⟨_,mem_image_of_mem _ h,mem_image_of_mem _ hx⟩
  rintro ⟨v,h',hx⟩; obtain ⟨z,hv,hj⟩:=mem_image.mp h'; obtain ⟨y,hy,hr⟩:=mem_image.mp hx
  -- compare labels via hZ; priority
  exact ⟨z,hv, ((Meadow.garden hC x hZ) (hf _ hy) (hf _ hv) (hr.trans hj.symm)) ▸ hy⟩
lemma stitches (z:Wreath C F) (hv:Mossy I' z) (hk:x∈summitV I' z) (hH:2 * D< c.val) : Mossy I (lesson (L) z) ∧ (L).low.cut x∈summitV I (lesson (L) z):= by
  have hS:= palace _ hv x hk
  refine ⟨⟨hv.size,fun i=> ?_,((receipts (I':=I') hC he x (I:=I) hp z hH hS hv.each) ▸ hv.moves)⟩,?_⟩
  · apply (orderR («K»:=I) (K':=I') hC he hp _ (rings hC he x z hv hk hH i) ((Meadow.garden hC x hH).mono _)).2 (hv.each i)
    exact coe_subset.mpr ((eachV (z:=z) i).trans hS)
  rw [pitchRoll (I:=I) (I':=I') hC he hp z]; exact mem_image_of_mem _ hk
end YM.QCD.Moss
