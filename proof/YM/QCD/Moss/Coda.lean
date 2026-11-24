import YM.QCD.Moss.Key
import YM.QCD.Moss.Rhino
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
variable {c f C F L:Side}{N D:ℕ} {I J:Type}
variable {P: Teller su} {S: StepData c f} {R: Rep su f}{T:Tube su S}{κ W μ τ:ℝ}
variable {X : ConnectedActivityE6.Target su P} {o:ConnectedActivityE6.Target.Order su W}
variable (K: Cash W τ μ L X o κ T R)
open Fork Run Port Kit Gas GasP Ursell
variable {K}
structure Bouquet (K:Cash W τ μ L X o κ T R)(I:Fleet K J N) where
 route : DarkV c f ↪ J
 frame i : I.window (route i)=wades S (radiusB τ) i
 home i : I.ground (route i)=halo (30*radiusB τ) (wades S (radiusB τ) i)
 born i : I.limit (route i)=∅
 parts i j : I.compat (route i) (route j)
namespace Bouquet
variable {D' : Fleet K J N}(Y:Bouquet K D')
def queen : PeaceV c f ↪ Piece S J:= {toFun:= Sum.map (disc S) Y.route,inj':=by rintro (x|x) (y|y)<;>simp}
def springV (v:BloomV c f): Pipe.Clump S J:=v.map Y.queen
lemma spring_cash (v:BloomV c f):Y.springV v=(Mint.hatch S v.toLeft).disjSum (v.toRight.map Y.route):=by
   ext i; constructor
   · intro h; obtain ⟨j,hj,rfl⟩:= mem_map.mp h; rcases j with j|j
     · exact inl_mem_disjSum.mpr (mem_map_of_mem _ (mem_toLeft.mpr hj))
     exact inr_mem_disjSum.mpr (mem_map_of_mem _ (mem_toRight.mpr hj))
   intro h; rcases i with i|i
   · obtain ⟨j,hj,rfl⟩:= mem_map.mp (inl_mem_disjSum.mp h); exact mem_map_of_mem Y.queen (mem_toLeft.mp hj)
   obtain ⟨j,hj,rfl⟩:=mem_map.mp (inr_mem_disjSum.mp h); exact mem_map_of_mem Y.queen (mem_toRight.mp hj)
lemma petalsC (v:BloomV c f): (Y.springV v).toLeft=hatch S v.toLeft ∧ (Y.springV v).toRight=v.toRight.map Y.route:=by rw [spring_cash]; simp
lemma shards : estateP K= D'.shellF.gP ∘ Y.queen:=by
    funext i; rcases i with i|i; · rfl
    exact (Y.home i).symm
lemma nestV (v:BloomV c f): floorV K v = D'.fullA (Y.springV v) :=by
    unfold floorV; rw [Y.shards]; change _=(v.map Y.queen).biUnion _; ext i; constructor
    · intro h; obtain ⟨j,hj,hx⟩:=mem_biUnion.mp h; exact mem_biUnion.mpr ⟨_,mem_map_of_mem Y.queen hj,hx⟩
    intro h; obtain ⟨j,hj,hx⟩:= mem_biUnion.mp h; obtain ⟨j,hj',rfl⟩:= mem_map.mp hj; exact mem_biUnion.mpr ⟨_, (by assumption),hx⟩
lemma fertile (v:BloomV c f): Ac.Spark (estateP K) v ↔ Ac.Spark D'.shellF.gP (Y.springV v):=by
    rw [Y.shards]; unfold springV; rw [map_eq_image]; convert! Meadow.sparkling (f:=Y.queen) _ v Y.queen.injective.injOn
lemma husk (v:BloomV c f): (roster (Y.springV v).toLeft)=⟨∅,∅,∅⟩:=by rw [(Y.petalsC v).1,Mint.unrostered]
lemma sprocket (v:BloomV c f): D'.shellF.born (Y.springV v):=by
   unfold Pipe.born; rw [(Y.petalsC v).1,(Y.petalsC v).2]
   refine ⟨Mint.hatchT .., ?_,?_⟩
   · intro i hi j hj h; obtain ⟨i,hi,rfl⟩:=mem_map.mp hi; obtain ⟨j,hj,rfl⟩:=mem_map.mp hj; exact Y.parts i j
   rw [(Mint.not_used ..).2]; symm; unfold filterP; ext i; simp_rw [Finset.notMem_empty, iff_false,mem_biUnion]; rintro ⟨p,hp,hx⟩; obtain ⟨j,hj,rfl⟩:=mem_map.mp hp; change i∈D'.limit (Y.route j) at hx; rw [Y.born] at hx; exact Finset.notMem_empty _ hx
lemma genuine (v:BloomV c f)(hp:Fiat K v): Given D' (Y.springV v) ∧ (roster (Y.springV v).toLeft).flags=∅:=
   ⟨⟨(Y.nestV v) ▸ plowed K hp,(Y.fertile v).1 hp.hot,Y.sprocket v⟩,congr_arg _ (Y.husk v)⟩
def kernelV (v:BloomV c f)(hp:Fiat K v) : Bright D':=⟨Y.springV v,Y.genuine v hp⟩
lemma aq (p q:BloomV c f)(hv:Fiat K p)(hx:Fiat K q): Y.kernelV p hv=Y.kernelV q hx ↔ p=q:=by
   refine ⟨fun he=> Finset.map_injective Y.queen (congr_arg Subtype.val he),?_⟩; rintro rfl; rfl
def heightV (r:Wreath c f)(h:Mossy K r): Clusters D'.Bright:=⟨r.1,fun i=>Y.kernelV (r.2 i) (h.each i)⟩
lemma shower (p: Wreath c f)(hp:Mossy K p): seatP D'.lightF (Y.heightV p hp) = summitV K p:=by
    unfold seatP heightV summitV unionOf; congr 1; funext i; exact (Y.nestV _).symm
lemma strings (p:Wreath c f)(hp:Mossy K p): coefficient (blocked D'.lightF) (Y.heightV p hp).2=coefficient (blocked (floorV K)) p.2:=by
    apply Meadow.movement; intro i j; apply or_congr ((Y.aq _ _ (hp.each i) (hp.each j)))
    change Ac.meets D'.lightF _ _ ↔Ac.meets (floorV K) _ _; unfold Ac.meets; simp_rw [nestV (Y:=Y)]; rfl
lemma warranty : Injective (fun i:{z// Mossy K z}=> Y.heightV i.val i.property):=by
    rintro ⟨⟨i,z⟩,hp⟩ ⟨⟨j,k⟩,hx⟩ he; obtain rfl:i=j:=congr_arg Sigma.fst he; change Sigma.mk i _=Sigma.mk i _ at he; injection he with h hh
    have hg:z=k:=funext fun i=> (Y.aq _ _ _ _).1 (congr_fun hh i); cases hg; rfl
end Bouquet
open Leaf Tee Orbit Garden Jets Flume Run YM.Next.Free
variable {δ β b:ℝ}{R:BudgetPoint} {K:Cash W τ μ L X o κ T (trimP T R δ β b)} (J': Fleet K I N) {j k:ℕ}{O:Flight j k}{h:f.val=c.val*O.L.val}{A ξ p z Y:ℝ}{π : St f}{U:ℕ→Atom su 2} {B:Plan k}
variable (F': Swathe O h π U B A ξ p z Y D)(Γ:Land c (Site c) (Site c))
abbrev artV : Fleet K (I⊕ Varn f c⊕ Gaze c) N:= united J' (united (VarnC K F' N) (sailP K Γ N))
def tiro: Bouquet K (artV J' F' Γ) :=by
    let f: DarkV c f ↪ I⊕ Varn f c⊕ Gaze c:=⟨Sum.inr ∘ washed c f, Sum.inr_injective.comp (washed c _).injective⟩
    refine ⟨f,?_,?_,?_,?_⟩
    · rintro (i|i)<;> rfl
    · rintro (i|i)<;> rfl
    · rintro (i|i)<;> rfl
    rintro (i|i) (j|j)<;>trivial
end YM.QCD.Moss
