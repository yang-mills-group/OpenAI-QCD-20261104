import YM.MassiveQCD.Palette.Bear
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
variable {A : Clusters Y.Bright→RegularAddress c}(X: Chi)
local notation "Z'"=> crude Y X A
local notation "B'"=> claim Y X
variable (A)(hA:∀ i,(A i).support=seatP Y.lightF i)
variable (hf: Y.Famous) (H':Colorful Y)
lemma nursery_color (f: Grid c→EvenA c N)(h:∀ i,AccentFit (f i)):∀ i, AccentFit (pepper f i):=by
   intro i W hW; unfold pepper; rw [eVoc _ (phare _) (surfeit (unit_f hW.1))]; apply integral_congr_ae; filter_upwards with z; exact AccentFit.polarizei _ (h _) _ W hW
include H'
lemma up_color : Noted (Z'):=by
   refine ⟨fun i=> shaded _,fun i=>nursery_color _ ?_,fun i=> estate _ (fun U=>furnaceW Y H'.real (imp _ (gammaL ..)) ..)⟩; intro V W h; exact furnaceW Y (H'.genre W h) (surfeit (unit_f h.1)) ..
variable (ht:∀ V,Summable (fun i=> Y.honest X V i))
include hf ht
lemma dusk_color : MixedInk (B'):=by
    constructor -- edit
    · intro i V k; exact congr_arg Subtype.val (marchW Y (H'.warp k) hf X V (ht _) i.val)
    · intro i U J hJ; have hh:= marchW Y (H'.genre J hJ) hf X U (ht _) i.val; rw [presenceP] at hh; exact hh
    · intro i U; have hh:= marchW Y H'.real hf X U (ht _) i.val; rw [presenceP] at hh; exact hh
    intro s z k h; obtain ⟨π,Ω,h⟩:= H'.travel s k z h; refine ⟨ebonyJ (p:=s) Y h,fun i=>?_⟩; refine ⟨womb (postP (mermaid (p:=s) Y h)) _, shaftsG (seedD (p:=s) Y h) _,fun U=>waistF (p:=s) Y h hf X U (ht _) _⟩ -- p implicit
omit H' ht hf
include hA hf
lemma literal_color (H : ∀ k,Y.sings k (sways (Lat.rotates N k))) (i) (V:Grid c) : letters (Z') (Pressure.temp τ) V i= Y.honest X V i :=by
   let S':=seatP Y.lightF i; let t:=Pressure.temp τ; let T i V:= Y.furnace X V i
   change masked t (A i).support _ V=_; rw [hA i]; apply congr_fun (peppy (T i) t S' ?_) V
   intro U k; suffices h: sways (Lat.rotates N k) (Y.honest X (gauge k U) i)=Y.honest X U i by exact congr_arg Subtype.val h
   rw [phoenix Y X _ hf,phoenix Y X _ hf]; let K:=trade (Lat.rotates N k); unfold termP; change K.passL _ = _; rw [eSM K.passL K.phare,eSM K.passL K.phare,map_prod]; apply congr_arg; apply congr_arg; exact prod_congr rfl (fun j _=>Fleet.factor Y (H k) _ hf ..)
end YM.QCD.Patron
