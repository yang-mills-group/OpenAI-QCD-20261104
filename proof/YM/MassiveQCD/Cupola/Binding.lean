import YM.MassiveQCD.Cupola.Foil
import YM.MassiveQCD.Palette.Hang
/-! # Footprints on every mark of a Root-Fleet with monotone projection.
 Each E letter retains full angular orientation in hue space.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Loom.Fleet
open ConnectedActivityE6 Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets Horticulture Mixed Reserves Trees Beam Cove Leaf Lat PhysicalNext.Repeat.Greenbelt MassiveQCD MassiveQCD.Cupola MassiveQCD.Ribbon
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{δ β τ μ W C:ℝ} {R:Rep su f}{F Z:Tree.Forest S.ratio}{Q:Target su P}{o :Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι I:Type}{N:ℕ}
local notation "W'"=> Pipe.Clump S ι
variable (N)[Fintype I](p:I→Site c)(φ:ℝ)(q:I→Bool)(Y:Fleet H ι (ample N I))
local notation "M"=> Ribbon.ample N I
local notation "mk"=> Mint N p φ q
local notation "wk"=> Well N p φ q
set_option quotPrecheck false
open Art Blaze Polar Shield Frond
open Grass Cove Lat GasP Filter Ursell Graph
open Sway OrbitG Villa Loom Bay Strut Patron
open MassiveQCD.Cupola
variable (D:ι→Finset I)
noncomputable def deathT (D:ι→Finset I)(s:W'):= s.toRight.biUnion D
structure Regal : Prop where
   marks (i :ι)(U:Grid f)(V:Grid c): Mint N p φ q (D i) (Y.works i U V)
variable (h:Regal N p φ q Y D) (hp:0<φ)
section transfer
include h hp
variable {J:Type}[Fintype J] (X:Coat T F)(s:Pipe.Clump S ι)(z:Air f su)(χ:Chi)(U:Grid c)
omit h in
private lemma choosing (f:J→EvenA c M)(s:Finset I)(hx:∀ i,mk s (f i)): mk s (choiceS f):= Mint.euro hp _ (Mint.sum hp _ _ _ (fun i _=>hx i))
lemma wrest (I': Finset (Tubular f su))(x:F.Slice su)(z:Body (↥I')) : mk (deathT D s) (Y.regards I' s X x z):=by
    apply Mint.euro hp; apply Mint.euro hp; apply Mint.product; exact fun i _=> Mint.euro hp _ (h.marks ..)
lemma lunge : mk (deathT D s) (Y.bandL s X):=by unfold bandL; split; exact choosing N p φ q hp _ _ fun _=> Mint.integral hp _ _ _ fun _=> Mint.integral hp _ _ _ fun _=> wrest N p φ q Y D h hp ..; exact Mint.none _
lemma swingM (t:Clusters Y.Bright):
   mk (Finset.univ.biUnion fun i=> deathT D (t.2 i).val) (Y.furnace χ U t):=by unfold furnace; apply Mint.euro hp; apply Mint.euro hp; apply Mint.product; exact fun i _=> choosing N p φ q hp _ _ fun _=> lunge N p φ q Y D h hp ..
noncomputable def swingE (t:Clusters Y.Bright):Finset I:=Finset.univ.biUnion fun i=> deathT D (t.2 i).val
lemma crudeM (t:Clusters Y.Bright) (A:Clusters Y.Bright→RegularAddress c):
   mk (swingE N Y D t) ((crude Y χ A).view t U):= by apply Mint.integral hp; exact fun i=> Mint.color hp _ (swingM N p φ q Y D h hp χ _ t)
lemma quests : mk (deathT D s) ((Y.suitcase F).shootsP X s):=by unfold Pipe.shootsP; split; exact choosing N p φ q hp _ _ fun _=> Mint.integral hp _ _ _ fun _=> Mint.euro hp _ (Mint.product D s.toRight _ (fun i _=> Mint.euro hp _ (h.marks ..))); exact Mint.none _
lemma markets : mk (deathT D s) (Y.vF s χ U):= choosing N p φ q hp _ _ fun _=> quests N p φ q Y D h hp ..
-- forced
lemma mottoM (s:Y.Wort)(hf:Y.Famous): wk (mission Y χ U s):=by
   unfold mission motto; split; swap; · exact Well.zeroV
   refine Well.product _ _ fun i _=>?_ ; rcases i with i|i; exact (markets N p φ q Y D h hp i.val χ U).launch
   change wk (NormedSpace.exp _-1); rw [sub_eq_add_neg]; refine Well.plus hp (Well.flash (Well.minus hp ?_)) (Well.minus hp Well.oneV); apply Well.total hp; intro j
   split; swap; · exact Well.zeroV
   next H=>
     rw [← phoenix Y χ U hf]; unfold honest; by_cases hz:Healthy (Pressure.temp τ) (seatP Y.lightF j) U
     · rw [masked_eq _ _ _ _ hz]; exact (swingM N p φ q Y D h hp χ U j).launch
     rw [masked_ne _ _ _ _ hz]; exact Well.zeroV -- colored unused!
end transfer
end YM.QCD.Loom.Fleet
#print axioms YM.QCD.Loom.Fleet.mottoM
