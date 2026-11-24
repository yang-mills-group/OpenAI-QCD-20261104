import YM.Play.Park
import YM.Hypnos.Rot
import YM.MassiveQCD.Cupola.Binding
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace YM.MassiveQCD.Play
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon Apron
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{β τ C μ W:ℝ}
variable {R:Rep su f}{O:BudgetPoint}{F:Tree.Forest S.ratio}{Q:Target su P}{o:Target.Order su W}
variable {ι κ I E J D:Type}{N:ℕ}
variable {δ b:ℝ} (H:Cash W τ μ L Q o C T (trimP T O δ β b)){P₀:Rise f N E J}
variable (G:Send S.ratio N D) (M:Fj D E J→Support c)
variable [Fintype I]
variable (X:Stitch.Tablet P₀ I)(z:I→Site f)(a:ℝ)
local notation "t"=>O.threshold
local notation "M'"=> Ribbon.ample N I
local notation "z'"=> S.ratio.parent ∘ z
local notation "I'"=> Ribbon.Spine I
open Stitch
local notation "Β"=>banknote N z' a
variable (Y:Fleet H κ (ample N I))
local notation "Ξ"=> closet H G M X z a
local notation "Tx"=> united (Ξ) Y
variable {q':I→Bool}(hw:X.Wave O.threshold q' z)(hk:Cove.Count G P₀ M)
namespace Camp
open TabletV
variable (p: Finset (Fj D E J))
local notation "V'"=> Wound M
local notation "P'"=> Piece S (Wound M ⊕ κ)
local notation "p'"=> plume P₀ G M p
variable (χ:Chi)(U:Grid c)
open PhysicalNext.Repeat.Greenbelt
variable (hs : ∀ j∈ leftE p, (X.spine j).Nonempty) (he:spent p=∅)
set_option quotPrecheck false
local notation "H'"=> student H G M X z a Y p hk hw hs he
local notation "Zs"=> campus H G M X z a Y p hk hw hs he
local notation "Ip"=> ↥(plume P₀ G M p)
-- shape from native flat steps, scheduling after pricing threshold history etc
variable {n r d:ℕ}
def Ray (z:I→Site c)(r:ℕ)(i:I): Support c:= halo r {z i}
lemma portion (z:I→Site c)(r)(i y): y∈ Ray z r i↔ separation (z i) y ≤ r:=by rw [Ray,halo_spec]; exact ⟨fun ⟨_,hx,hp⟩=> mem_singleton.mp hx ▸ hp,fun hp=>⟨_,mem_singleton_self _,hp⟩⟩
structure Gowns (n:ℕ) : Prop where
    mint : M = roof G P₀ 30 (radiusB τ)
    trim : G.trim ≤ radiusB τ
    flare : 0<radiusB τ
    pulls : ∀ i∈ ops p,∀ j∈ G.rooms i, G.rooms i ⊆ halo (radiusB τ) {j}
    thorn :∀ i ∈ leftE p, ∀ j∈ X.spine i, (P₀.row i).support.image S.ratio.parent ⊆ Ray (S.ratio.parent∘z) n j
local notation "Nr"=> n + 45*radiusB τ
local notation "Rt"=> Ray (z') (n + 45*radiusB τ)
variable (hS:Gowns G M X z p n (τ:=τ))
include hS
lemma wingedE {i:E} {j:I}(hj:i∈ leftE p)(ht:j∈X.spine i): M (.inr (.inl i)) ⊆ (Rt) j := by
    rw [hS.mint]; let W:= (P₀.row i).support; have hp:= hS.thorn _ hj _ ht
    intro k hk; obtain ⟨w,hw,hz⟩:=halo_spec.mp ((roofs G P₀ 30 _ hS.trim hS.flare).2 _ hk); refine (portion _ _ _ _).mpr ((separation_triangle ((z') j) w k).trans ?_)
    have h':= (portion _ _ _ _).mp (hp (show w∈W.image S.ratio.parent from hw)); omega
include he hs
lemma regions (i:Finset (Fj D E J))(hp: i⊆p)(hV:Burke P₀ G i) : ∀ j∈i,∃ k∈ X.markers i,M j⊆ (Rt) k :=by
   let F j (h:j∈leftE i): j∈leftE p:=mem_toLeft.mpr (mem_toRight.mpr (hp (mem_toRight.mp (mem_toLeft.mp h))))
   rintro (j|j|j) hj
   · have hm: j∈ ops i:= mem_toLeft.mpr hj; obtain ⟨k,hk,hw⟩:=Finset.not_disjoint_iff.mp (hV j hm); obtain ⟨b,hb,ht⟩:=mem_biUnion.mp hk; obtain ⟨l,hl⟩:=hs b (F b hb); refine ⟨l,mem_union_left _ (mem_biUnion.mpr ⟨_,hb,hl⟩),?_⟩
     have hx:=hS.thorn _ (F b hb) _ hl (mem_image_of_mem _ ht); have hv:= (portion _ _ _ _).mp hx
     intro y hy; rw [hS.mint] at hy; obtain ⟨w,hw',hh⟩:=halo_spec.mp ((roofs G P₀ 30 _ hS.trim hS.flare).2 _ hy); obtain ⟨v,hV,rfl⟩:= mem_image.mp hw'; have hB:(separation k v) ≤ radiusB τ:= by
        obtain ⟨x,hx,h⟩ :=halo_spec.mp (hS.pulls j (mem_toLeft.mpr (hp hj)) k hw (show v∈ G.rooms j from hV)); rw [mem_singleton.mp hx] at h; exact h
     refine (portion _ _ _ _).mpr ((separation_triangle _ (S.ratio.parent k) _).trans ?_); have h:= Work.E04.parent_separation S.ratio k v; have hs:=separation_triangle (S.ratio.parent k) (S.ratio.parent v) y; have hp:=hS.flare; omega
   · have hm:j∈leftE i:= mem_toLeft.mpr (mem_toRight.mpr hj); obtain ⟨k,hk⟩:=hs j (F _ hm); exact ⟨k,mem_union_left _ (mem_biUnion.mpr ⟨_,hm,hk⟩),wingedE G M X z p hS (F _ hm) hk⟩
   have hh:j∈ spent p:=mem_toRight.mpr (mem_toRight.mpr (hp hj)); rw [he] at hh; exact (notMem_empty _ hh).elim
variable (y:Wound M)(hp:y.val⊆p)(hV:Burke P₀ G y.val)
local notation "mk"=> X.markers y.val
include hp hV
lemma panorama : y.val.biUnion M ⊆ (mk).biUnion Rt:=by
    intro i hi; obtain ⟨j,hj,h⟩:=mem_biUnion.mp hi; obtain ⟨k,hk,hv⟩:=regions G M X z p hs he hS _ hp hV j hj; exact mem_biUnion.mpr ⟨k,hk,hv h⟩
include hw hk
lemma kerchief : Ac.Spark Rt (mk):=by
   let s:=y.val; have hh:= y.property; have hm:= hh.2; let V:=mk; have hg:=regions G M X z p hs he hS _ hp hV
   have ht:(V).Nonempty:=by obtain ⟨i,hi⟩:=hh.1; obtain ⟨k,hk,-⟩:=hg i hi; exact ⟨k,hk⟩
   -- lift chain intersections through dirs
   have hp i j (h: link M s i j): ∀ a∈V,∀ b∈V, M i⊆ (Rt) a → M j⊆ (Rt) b → (M i).Nonempty → (M j).Nonempty→ Ac.chain Rt V a b:=by
        induction h with
        | refl=> rintro a ha b hb h h' ⟨k,hk⟩ _; exact .single ⟨ha,hb,k,h hk,h' hk⟩
        | @tail i j _ h ih=>
          intro a ha b hb hi hj ha' hb'; obtain ⟨hi',hj',k,hk₀,hk'⟩:=h; obtain ⟨c,hc,hC⟩:=hg i hi'
          exact .tail (ih a ha _ hc hi hC ha' ⟨_,hk₀⟩) ⟨hc,hb,k,hC hk₀,hj hk'⟩
   have he(i:E)(hi:i∈leftE s)(b:I)(hb:b∈X.spine i) : (z') b∈ M (.inr (.inl i)) :=by
       apply hk.budget; exact mem_image_of_mem _ (halo_subset _ _ (hw.spotE i (mem_image_of_mem _ hb)))
   refine ⟨ht,?_⟩; intro a ha b hb; let f i:= M (.inr (.inl i)); have hy : V=(leftE s).biUnion X.spine :=by
       unfold V Stitch.Tablet.markers; rw [spentP _ _ ‹y.val⊆p› ‹spent p=∅›,biUnion_empty,union_empty]
   obtain ⟨i,hi,he'⟩:=mem_biUnion.mp (show a∈ (leftE s).biUnion X.spine from hy ▸ ha); obtain ⟨j,hj,hg⟩:=mem_biUnion.mp (show b ∈ (leftE s).biUnion X.spine from hy ▸ hb); refine hp _ _ (hm _ (mem_toRight.mp (mem_toLeft.mp hi)) _ (mem_toRight.mp (mem_toLeft.mp hj))) _ ha _ hb ?_ ?_ ⟨_,he i hi a he'⟩ ⟨_,he j hj b hg⟩
   · exact wingedE G M X z p hS (mem_toLeft.mpr (mem_toRight.mpr (‹y.val⊆p› (mem_toRight.mp (mem_toLeft.mp hi))))) he'
   exact wingedE G M X z p hS (mem_toLeft.mpr (mem_toRight.mpr (‹y.val⊆p› (mem_toRight.mp (mem_toLeft.mp hj))))) hg
omit hk hw hp hV
lemma frond (o:Support c)(hh:∀ i∈ leftE p,∀ j∈ X.spine i,(Rt) j⊆ o): owned (P₀:=P₀) G M p o:=by
   intro i hi hp j hj; obtain ⟨k,hk,hj'⟩:=mem_biUnion.mp hj; obtain ⟨w,hw,hQ⟩:= regions G M X z p hs he hS i hi hp k hk; have ht:w∈(leftE i).biUnion X.spine:=by
      unfold Stitch.Tablet.markers at hw; rwa [spentP _ _ hi he,biUnion_empty,union_empty] at hw
   obtain ⟨x,hx,ht⟩:=mem_biUnion.mp ht; exact hh x (mem_toLeft.mpr (mem_toRight.mpr (hi (mem_toRight.mp (mem_toLeft.mp hx))))) w ht (hQ hj')
end Camp
end YM.MassiveQCD.Play
#print axioms YM.MassiveQCD.Play.Camp.frond
#print axioms YM.MassiveQCD.Play.Camp.kerchief
#print axioms YM.MassiveQCD.Play.Camp.panorama
