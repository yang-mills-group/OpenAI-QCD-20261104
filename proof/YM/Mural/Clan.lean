import YM.Mural.Fil
import YM.Mural.Hind
import YM.Mural.Owner
/-! # Linear-array outputs along footprints. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Loom.Fleet.Palette
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets Horticulture
open Mixed Reserves Trees Beam Cove Leaf Lat PhysicalNext.Repeat.Greenbelt Grass
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{δ β τ μ W C:ℝ}{R:Rep su f}{F Z:Tree.Forest S.ratio}{Q:Target su P}{o :Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι I:Type}{M:ℕ}
open Art Hues QCD.Sway QCD.Sway.OrbitG GasP Ursell Graph
open MassiveQCD MassiveQCD.PaletteT MassiveQCD.Plate MassiveQCD.Ribbon MassiveQCD.Cupola
local notation "C'"=>Coat T
variable (N:ℕ)[Fintype I]
local notation "FI"=>Option I
local notation "I'"=>Pipe.Clump S ι
variable (Y:Fleet H ι M) (p:Unit→Site c) (v:ℝ)(q:Unit→Bool)(Γ:Option I→ ι→Grid f→ Grid c→EvenA c (ample N Unit))
local notation "P'"=>EvenA c (ample N Unit)
variable (T0: Site c→ su.El)
variable (κ:Delta I)
structure Palm :Prop where
  signs : straight κ
  hale (i:ι)(U:Grid f)(V:Grid c): Dealers N p v q (fun k=> Γ k i U V)
  hearty i: (align Y (Γ i)).Famous
  dress (i:ι) (U:Grid f)(V:Grid c): Binds κ (actC (ample N Unit) T0) (fun j=> Γ j i (gauge (constantGauge T0 S.ratio) U) (gauge T0 V)) (fun j=> Γ j i U V)
local notation "Kp"=> actC (ample N Unit)
local notation "Y'" k=> align Y (Γ k)
variable (h:Palm N Y p v q Γ T0 κ)
include h
lemma basis : Kit Y Γ T0 (Dealers.clan (N:=N) (p:=p) (t:=v) (q:=q)) κ (actC (ample N Unit) T0):=⟨h.hearty,h.signs,h.dress,h.hale,Dealers.unit I,fun i j hi hj=>Dealers.combine hi hj,fun i j hi hj k m=>Dealers.blouse hi hj k m⟩
lemma foot_m (χ:Chi)(D:Grid c)(u:Y.Wort)(hv:∀ i v,Summable (honest (align Y (Γ i)) χ v)): Binds κ (Kp T0) (fun i=>(Y' i).mission χ (gauge T0 D) u) (fun i=>(Y' i).mission χ D u)∧ Dealers N p v q (fun i=> (Y' i).mission χ D u):=matte Y _ _ (basis N Y p v q Γ T0 κ h) χ D u hv
lemma foot_e (χ:Chi)(D:Grid c)(u:Clusters Y.Bright): Binds κ (Kp T0) (fun i=>(Y' i).honest χ (gauge T0 D) u) (fun i=>(Y' i).honest χ D u)∧ Dealers N p v q (fun i=> (Y' i).honest χ D u):= atTerrace Y _ _ (basis N Y p v q Γ T0 κ h) χ D u
omit h
variable {Z:Finset (Site c)} -- protected hull condition

-- scoping can be applied singly. survive at final
section offset
variable (S: Finset Unit) -- unused
end offset
end YM.QCD.Loom.Fleet.Palette
namespace YM.QCD.Loom.Fleet
open ConnectedActivityE6 Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets Horticulture Mixed Reserves Trees Beam Cove Leaf Lat PhysicalNext.Repeat.Greenbelt MassiveQCD MassiveQCD.Cupola MassiveQCD.Ribbon PaletteT
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{δ β τ μ W C:ℝ} {R:Rep su f}{F Z:Tree.Forest S.ratio}{Q:Target su P}{o :Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι:Type}{N:ℕ}
open Art Blaze Polar Shield Frond
open Grass Cove Lat GasP Filter Ursell Graph
open Sway OrbitG Villa Loom Bay Strut Patron
variable (N) (p:Unit→Site c)(φ:ℝ)(q:Unit→Bool)(Y:Fleet H ι (ample N Unit)) (D:ι→Finset Unit)
variable (U V: Grid c)
variable (Wc: Support c)(hX:∀ i,(D i).Nonempty → Wc⊆Y.ground i) (h:Regal N p φ q Y D)(hp:0<φ)
variable (χ:Chi) (hf:Y.Famous)
include hX
lemma scope_p (u:Pipe.Clump S ι)(hv:(deathT D u).Nonempty): Wc⊆ Y.fullA u:=by
    obtain ⟨i,hi⟩:=hv; obtain ⟨j,hj,hi⟩:=mem_biUnion.mp (show i∈u.toRight.biUnion D from (by unfold deathT at hi; convert! hi)); exact (hX j ⟨i,hi⟩).trans (Y.shellF.leP _ hj)
lemma scope_l (u:Clusters Y.Bright)(hv:(swingE N Y D u).Nonempty): Wc⊆ GasP.seatP Y.lightF u:=by
    obtain ⟨i,hi⟩:=hv; obtain ⟨j,hj,h⟩:=mem_biUnion.mp (show i∈ (univ.biUnion fun j=> deathT D (u.2 j).val) from (by unfold swingE at hi; convert! hi)); exact (scope_p N Y D Wc hX (u.2 j).val ⟨_,h⟩).trans (subset_biUnion_of_mem (fun j=>Y.lightF (u.2 j)) (mem_univ j))
omit hX
open NormedSpace
lemma tsum_memberD {V:Type*}{N:ℕ}(A:Subalgebra ℂ (EvenA c N))(Y:V→EvenA c N)(he:∀ i,Y i∈ A): (∑' i,Y i)∈A:=by
     by_cases h:Summable Y; · exact A.toSubmodule.closed_of_finiteDimensional.mem_of_tendsto h.hasSum (Eventually.of_forall fun i: Finset V=> Submodule.sum_mem A.toSubmodule (fun j _=>he j))
     rw[tsum_eq_zero_of_not_summable h]; exact A.zero_mem
lemma exp_memD {N:ℕ}(A:Subalgebra ℂ (EvenA c N))(y)(h:y∈A): exp y∈A:= by
   have hp(n:ℕ): ((n.factorial:ℂ)⁻¹) • y^n ∈A:= A.toSubmodule.smul_mem _ (A.pow_mem h _); exact (exp_series_hasSum_exp' (𝕂:=ℂ) y).tsum_eq ▸ tsum_memberD A _ hp
include hX
include h hp hf
lemma away (s:Y.Wort)(hx: ¬ Wc ⊆ wound Y.broad s): Mint N p φ q ∅ (Y.mission χ V s):=by
   let A:= pocket N p φ q hp
   unfold Fleet.mission motto; split; swap; · exact Mint.none _
   next hS=>
      apply A.prod_mem; rintro (i|i) hi
      · let Z:= deathT D i.val; have hp' : Z=∅:=by
           apply Finset.not_nonempty_iff_eq_empty.mp; intro h; exact hx ((scope_p N Y D Wc hX _ h).trans (show _⊆wound Y.broad s from subset_biUnion_of_mem (facesP Y.broad) hi))
        change Mint N p φ q ∅ (Y.vF i.val χ V); rw [← hp']; exact markets N p φ q Y D h hp i.val χ V
      change NormedSpace.exp (-GasP.portion Y.lightF (Y.dawnV χ V) i)-1∈ A; apply A.sub_mem _ A.one_mem; refine exp_memD A _ ?_ ; apply A.neg_mem; unfold portion; -- helper subalgebra exp/tsum no assumptions..
      apply tsum_memberD A; intro j; split; next hr=>
        have hP: swingE N Y D j=∅:=by
            apply Finset.not_nonempty_iff_eq_empty.mp; intro h; exact hx ((scope_l N Y D Wc hX j h).trans ((show GasP.seatP Y.lightF j=i from hr).le.trans (show i⊆GasP.wound Y.broad s from subset_biUnion_of_mem (facesP Y.broad) hi))) -- hr issues
        rw [← phoenix Y χ V hf]; change Mint _ _ _ _ _ _; unfold honest; by_cases he:Healthy (Pressure.temp τ) (GasP.seatP Y.lightF j) V
        · rw [masked_eq _ _ _ _ he]; exact hP ▸ swingM N p φ q Y D h hp χ V j
        rw [masked_ne _ _ _ _ he]; exact Mint.none _
      exact A.zero_mem
end YM.QCD.Loom.Fleet
#print axioms YM.QCD.Loom.Fleet.away
#print axioms YM.QCD.Loom.Fleet.Palette.foot_m
