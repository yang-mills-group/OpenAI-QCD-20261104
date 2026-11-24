import YM.QCD.Pant.Credits
/-! # Rain off flanks. Masks conserved. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Patron
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets Horticulture
open Mixed Reserves Trees Beam Cove Leaf Lat PhysicalNext.Repeat.Greenbelt Loom Fleet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{δ β τ μ W C:ℝ} {R:Rep su f}{F Z:Tree.Forest S.ratio}{Q:Target su P}{o :Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι:Type}{N:ℕ}
local notation "I"=> Pipe.Clump S ι
local notation "C'"=>Coat T
variable (Y:Fleet H ι N)
set_option quotPrecheck false
open Art Blaze Polar Shield Frond
open Grass Cove Lat GasP Filter Ursell Graph
open Sway OrbitG Villa Loom Bay Strut
variable {K: EvenA c N→+*EvenA c N}
-- Pan not on Gospel. duplicate to arbitrary Y.
structure Peace :Prop where
 travel (s:Strut c)(p :Spike)(g: Site c→ℂ): Warrant s g p→∃ (π:R.activities.Moves s.1 (S.ratio.embed s.2))(Ω:Equiv.Perm ι), Y.Marches π Ω (trade (copies N (Strut.haze s p g))).passL
 real : Y.sings (fun _=>1) (dawn (idol c N)).passL
 warp z: Y.sings z (trade (Lat.rotates N z)).passL
 genre (W:Matrix (Flavor N) (Flavor N) ℂ): W∈unitary _ → Y.sings (fun _=>1) (trade (flute (Lat.Row c) W)).passL

lemma naming (j:Clusters Y.Bright):∃ S: RegularAddress c,S.support=seatP Y.lightF j:=by
    let W:=j.2 none
    obtain ⟨p,hp⟩:=W.2.1.1; exact ⟨⟨p,_,mem_biUnion.mpr ⟨none, mem_univ _,hp⟩⟩,rfl⟩
variable {A : Clusters Y.Bright→RegularAddress c}(X: Chi)
-- exact real renormalizable expo *evaluation*. wrapping unmasked representative queries anchored; counts.
def crude (A:Clusters Y.Bright→RegularAddress c): Gem c N (Clusters Y.Bright):=⟨A,fun j V=> pepper (fun v=> Y.furnace X v j) V⟩
def claim : Rail c N Y.Faber:=⟨fun i=> ⟨wound Y.broad i.val,sweep Y.invD i.val,(Y.fuel i).1,(Y.fuel i).2⟩,fun i V=> Y.mission X V i.val⟩
variable (A)(hA:∀ i,(A i).support=seatP Y.lightF i)
local notation "Z'"=> crude Y X A
local notation "B'"=> claim Y X
variable (hf: Y.Famous) (hi: Territory.Gate Y)(hV:Y.Feasible) (hp:Y.speaking)
include hA hf hi hp
lemma plumE : (Z').Gather:=by
   constructor
   · intro j U V hk; have hh : Agrees (seatP Y.lightF j) U V:=hA _ ▸ hk; exact siteZ _ _ (Y.courtB hf hp X j).2 U V hh -- annotation
   · exact fun i=> wharf _ (Y.courtB hf hp X i).1
   intro i V; rw [show ((Z').addr i).support=_ from hA i]; exact plotP _ _ (fun V=> Y.sensesP hf hi X V i) V
omit hA
include hV
lemma plumK [Countable Y.Bright]: (B').Reg (Pressure.temp τ):=by
   have hh s:= Y.inletC hf hV hi hp X s
   refine ⟨fun i=> (hh i.val).2.1,fun i=>(hh i.val).1,fun i=>(hh i.val).2.2,?_⟩
   intro i U h; change Y.mission X U i.val≠0 at h; unfold mission motto at h; split at h
   next hj=> exact hj.2
   next _=> exact (h rfl).elim
omit hi hV hp hf
variable (H':Peace Y)
include H'
lemma upstream : Dyed (Z'):=by
   refine ⟨fun i=> shaded _,fun i=>nursery _ ?_,fun i=> estate _ (fun U=>furnaceW Y H'.real (imp _ (gammaL ..)) ..)⟩; intro V W h; exact furnaceW Y (H'.genre W h) (surfeit (unit_f h)) ..
variable (ht:∀ V,Summable (fun i=> Y.honest X V i))
include hf ht
lemma dusky : MixedP (B'):=by
    constructor -- edit
    · intro i V k; exact congr_arg Subtype.val (marchW Y (H'.warp k) hf X V (ht _) i.val)
    · intro i U J hJ; have hh:= marchW Y (H'.genre J hJ) hf X U (ht _) i.val; rw [presenceP] at hh; exact hh
    · intro i U; have hh:= marchW Y H'.real hf X U (ht _) i.val; rw [presenceP] at hh; exact hh
    intro s z k h; obtain ⟨π,Ω,h⟩:= H'.travel s k z h; refine ⟨ebonyJ (p:=s) Y h,fun i=>?_⟩; refine ⟨womb (postP (mermaid (p:=s) Y h)) _, shaftsG (seedD (p:=s) Y h) _,fun U=>waistF (p:=s) Y h hf X U (ht _) _⟩ -- p implicit
omit ht
include hA
lemma literalX (i) (V:Grid c) : letters (Z') (Pressure.temp τ) V i= Y.honest X V i :=by
   let S':=seatP Y.lightF i; let t:=Pressure.temp τ; let T i V:= Y.furnace X V i
   change masked t (A i).support _ V=_; rw [hA i]; apply congr_fun (peppy (T i) t S' ?_) V
   intro U k; suffices h: sways (Lat.rotates N k) (Y.honest X (gauge k U) i)=Y.honest X U i by exact congr_arg Subtype.val h
   rw [phoenix Y X _ hf,phoenix Y X _ hf]; let K:=trade (Lat.rotates N k); unfold termP; change K.passL _ = _; rw [eSM K.passL K.phare,eSM K.passL K.phare,map_prod]; apply congr_arg; apply congr_arg; exact prod_congr rfl (fun j _=>Fleet.factor Y (H'.warp k) _ hf ..)
include ht
lemma fullL (V:Grid c): HasSum (letters (glean (Z')) (Pressure.temp τ) V) (∑' i,Y.honest X V i):=by
    let E:=crude Y X A; let t:=Pressure.temp τ
    have hh V:letters E t V=fun i=> Y.honest X V i:=funext fun i=> literalX Y A X hA hf H' i V
    have hp V: Patron.total E t V=∑' i,Y.honest X V i:=tsum_congr (fun i=>congr_fun (hh V) i)
    rw [← hp]; refine ocean E (fun U=> (ht U).congr fun i=>(congr_fun (hh U) i).symm) (fun s U=>?_) V
    obtain ⟨π,e,hπ⟩:= H'.travel s (sat s) (ink s) (assured _); let L:= spice (N:=N) s; rw [hp,hp]; have hz:= ((ht (sky s U)).hasSum.map L (OrbitG.phare _))
    let A:= Patron.pack (adawn Y (p:=s) hπ); rw [← Equiv.tsum_eq A (fun i=>Y.honest X U i)]; refine hz.tsum_eq.symm.trans (tsum_congr fun i=>gistE Y (p:=s) hπ hf ..)
end YM.QCD.Patron
