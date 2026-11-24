import YM.QCD.Moss.Hero
import YM.QCD.Grove.Tower
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Nil
/-!
 # Low Pane. Finset cutoff held preserving costs. Fabric independent of old matter.
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
open Loom Fleet Patron Cove GasP
section lotus
variable {S:StepData c f}{R:RG.Rep su f}{T:Tube su S} {X: ConnectedActivityE6.Target su K} {o:ConnectedActivityE6.Target.Order su W}{D: Cash W p a L₀ X o U T R}
variable {I:Type}{N:ℕ}{B:Fleet D I N}
def billM (i: PeaceV c f): Nat := Sum.elim Meadow.held (fun _=>0) i
def Fetes (k: ℕ)(i:Wreath c f): Prop:=∀ j s, s∈ i.snd j→billM s ≤ k
def scroll (D: Cash W p a L₀ X o U T R)(k:ℕ): Finset (Wreath c f):=
   let T:Finset (PeaceV c f):=(Meadow.tuck k).disjSum univ
   ((Finset.range 2).sigma (fun i=> Fintype.piFinset (fun _j:Option (Fin i)=> T.powerset))).filter (Mossy D)
lemma leads (D: Cash W p a L₀ X o U T R)(k:ℕ)(i:Wreath c f): i∈scroll D k ↔ Mossy D i∧ Fetes k i:=by
   let M:Finset (PeaceV c f):=(Meadow.tuck k).disjSum univ
   have he x:x∈M ↔ billM x≤k:=by cases x with
                                   | inl i=> exact inl_mem_disjSum.trans (Meadow.pocket ..)
                                   | inr i=> exact iff_of_true (inr_mem_disjSum.mpr (mem_univ _)) (Nat.zero_le _)
   rcases i with ⟨m,u⟩; unfold scroll; rw [mem_filter,mem_sigma,Fintype.mem_piFinset]; simp_rw [mem_powerset]; apply Iff.intro
   · rintro ⟨⟨hk,h⟩,hp⟩; exact ⟨hp, fun j s hj=> (he s).1 (h j hj)⟩
   rintro ⟨hh,hz⟩; exact ⟨⟨mem_range.mpr (Nat.lt_succ_of_le hh.size),fun j s hj=> (he s).2 (hz j s hj)⟩,hh⟩
lemma lateM (D : Cash W p a L₀ X o U T R)(i:Wreath c f)(h:Mossy D i): ∀ᶠ k in atTop,i∈scroll D k:=by
    have hh j: ∀ᶠ k in atTop,∀ s∈i.2 j,billM s≤ k:= (eventually_all_finset _).mpr fun s _=> eventually_ge_atTop (billM s)
    exact (eventually_all.mpr hh).mono fun k hp=> (leads D k i).mpr ⟨h,hp⟩
def dashX (k:ℕ)(L:Bouquet D B): Finset (Clusters B.Bright):=
   (scroll D k).attach.image fun i=> L.heightV i.val ((leads D k i.val).1 i.property).1
lemma oceanM (L: Bouquet D B)(k:ℕ)(i: Clusters B.Bright): i∈dashX k L↔∃ j:Wreath c f,∃ h:Mossy D j,Fetes k j∧ L.heightV j h=i:=by
    constructor
    · intro h; obtain ⟨j,h,hz⟩:= mem_image.mp h; have hp := (leads D k j.val).1 j.property; exact ⟨j.val,hp.1,hp.2,hz⟩
    rintro ⟨j,h,he,rfl⟩; exact mem_image_of_mem (fun i:↥(scroll D k)=> L.heightV i.val ((leads D k i.val).1 i.2).1) (mem_attach _ ⟨_,(leads D k j).2 ⟨h,he⟩⟩)
end lotus
variable {N:ℕ}{T:Tube su (stepped Q h)}{T':Tube su (stepped Q H)} {X: ConnectedActivityE6.Target su K} {o:ConnectedActivityE6.Target.Order su W}
   {R:RG.Rep su f}{R':RG.Rep su F}{D: Cash W p a L₀ X o U T R} {D₀: Cash W p a L₀ X o V T' R'}
local notation "L" => Lace.project (h:=h) (H:=H) hC he
variable {I J:Type}{B:Fleet D I N}{Z:Fleet D₀ J N}
variable {Y:Bouquet D B}{Y':Bouquet D₀ Z}
include hC he
lemma feting (u: Wreath C F)(k:ℕ): Fetes k (lesson (L) u) ↔ Fetes k u:=by
    have he s: billM (staid (L) s)=billM s:=by rcases s with (s|s|s|s)|s<;>rfl
    constructor
    · intro h i s hs; rw [← he s]; exact h i (staid (L) s) (mem_image_of_mem _ hs)
    intro h i s hs; obtain ⟨j,hj,rfl⟩:=mem_image.mp hs; rw [he]; exact h i j hj
local notation "A₀"=> tideP X.halo (radiusB p)
variable (g:Site C→ℂ) (hp:Alive hC he B Z (Folding.axes (Lace.project (h:=h) (H:=H) hC he).low g N) Y Y')
include hp
abbrev seatX (D: Cash W p a L₀ X o U T R) (i:Site c)(k:ℕ): Finset (Wreath c f):=(scroll D k).filter fun v=> i∈summitV D v
lemma fibers (x:Site C)(k:ℕ)(hv: 2*(2*A₀+3)< c.val): ∃ u:(↥(seatX D₀ x k)≃ ↥(seatX D ((L).low.cut x) k)), ∀ i,(u i).val=lesson (L) i.val:=by
    let W:=A₀; let S:=seatX D ((L).low.cut x) k
    let P':=seatX D₀ x k
    have hv₁:2* A₀<c.val:=by omega
    refine permit (lesson (L)) P' S ?_ ?_
    · ext j; constructor
      · intro h; have hh := mem_filter.mp (show j∈seatX D ((L).low.cut x) k from h); have he':=(leads ..).1 hh.1
        obtain ⟨v,hv',hz,hp'⟩:= recap (Q:=Q) hC he x (I:=D) (I':=D₀) hp.birth j he'.1 hh.2 (show 2*(A₀+orbitD X.halo (radiusB p))< c.val from (by unfold tideP at *; omega))
        exact mem_image.mpr ⟨_,mem_filter.mpr ⟨(leads _ _ _).2 ⟨hv',(feting v k).mp (hp'.symm ▸ he'.2)⟩,hz⟩,hp'⟩ -- inferred
      intro hh; obtain ⟨i,hi,rfl⟩:=mem_image.mp hh; have hz:= mem_filter.mp (show i∈ seatX D₀ x k from hi); have he':= (leads ..).1 hz.1; have ht:= stitches (Q:=Q) hC he x (I:=D) hp.birth i he'.1 hz.2 hv₁
      exact mem_filter.mpr ⟨(leads ..).2 ⟨ht.1,(feting ..).mpr he'.2⟩,ht.2⟩
    intro i hi j hj hz; have hi':=mem_filter.mp (show i∈seatX D₀ x k from hi); have hj':=mem_filter.mp (show j∈seatX D₀ x k from hj); exact inquire (Q:=Q) hC he x j i ((leads ..).1 hj'.1).1 ((leads ..).1 hi'.1).1 hj'.2 hi'.2 hv₁ hz
end YM.QCD.Moss
