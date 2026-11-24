import YM.Massive.Commerce.Issue

/-!
# Degree-wise equivariance of the priced transfer (E,K)

Reserve arbitrary fixed *seed amplitudes* on internal E,K slots and tag a
copy by a marker magnitude $a_i$. This lemma computes **exactly** the price
factor relationship at the two raw transfers `master` and `shadow` with
such individual amplitude weights. It is thereby possible to use the estimates
on an *enhanced* master transfer. For E the amplitudes are to be in Mayer
coordinates. There is no "whole-disk factor" here; every vertex transforms
according to *its own* weight. The K output itself is not homogeneous;
its `duskV` ingredients before occupied-flag recombination and exclusion
corrections however are, with the `Shell` geometry unchanged.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Loom.Fleet
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets Horticulture
open Mixed Reserves Trees Beam Cove Leaf Lat PhysicalNext.Repeat.Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{δ β τ μ W C:ℝ} {R:Rep su f}{F Z:Tree.Forest S.ratio}{Q:Target su P}{o :Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι:Type}{N:ℕ}
local notation "I"=> Pipe.Clump S ι
local notation "C'"=>Coat T
variable (Y:Fleet H ι N)
set_option quotPrecheck false
local notation "V'"=> prism T τ
open Art Blaze Polar Shield Frond

open GasP Ursell Graph
variable (f':ι→Grid f→Grid c→EvenA c N) (A:ι → Prop)

-- Explicit reader variants so one can use `rfl` under reduction.
local notation "V₁"=> version Y f'
variable {χ: Chi}
variable (a:ι→ℂ)
-- Any draws multiply accordingly.
local instance : SMulCommClass ℂ ℝ (EvenA c N) where smul_comm x y z := (smul_comm y x z).symm
lemma divideC {J:Type}[Fintype J](s:ℂ) (u v:J→EvenA c N) (he:∀ i, v i=s • u i): choiceS v=s • choiceS u:=by unfold choiceS; rw [smul_comm s]; apply congr_arg; rw [show (s • ∑ x,u x)=∑ x,s • u x from smul_sum]; exact (sum_congr rfl fun i _=> he i)
variable (h: ∀ i U V, f' i U V=a i • Y.works i U V)
local notation "µ"=> fun z:Pipe.Clump S ι=>∏ i∈z.toRight,a i
include h
lemma lows_scaled (z:I)(x:Finset (Tubular f su))(X:Coat T F): (V₁).lows x z X=((µ) z) • Y.lows x z X:=by
    unfold lows; rw [← integral_smul]; apply integral_congr_ae; filter_upwards with t; rw [← integral_smul]; apply integral_congr_ae; filter_upwards with p
    dsimp only [regards]; rw [smul_comm ((µ) z),smul_comm ((µ) z)]; apply congr_arg; apply congr_arg
    apply Eq.trans _ (prod_smul z.toRight a _); apply prod_congr rfl; intro i _; unfold muscle; dsimp only; rw [h i]; exact smul_comm _ _ _
lemma brisk_scaled (z:I)(χ:Chi)(V:Grid c): brisk V₁ z χ V=((µ) z) • brisk Y z χ V:=by
    unfold brisk; apply divideC; intro i; unfold bandL; let Q:= Y.suitcase (allot i)
    change ite (Ac.Spark Q.gP z ∧ Q.born z) _ _ =((µ) z) • ite (Ac.Spark Q.gP z ∧ Q.born z) _ _
    split
    · exact divideC _ _ _ fun _=>lows_scaled Y f' a h z ..
    exact (smul_zero _).symm
lemma capacity_scaled (z:I)(k:Finset ℕ)(X:Coat T F)(y:Air f su): ((V₁).suitcase F).capacityP z k X y=((µ) z) • (Y.suitcase F).capacityP z k X y:=by
    unfold Pipe.capacityP; rw [smul_comm ((µ) z)]; apply congr_arg; apply Eq.trans _ (prod_smul z.toRight a _)
    unfold Pipe.averageP; apply prod_congr rfl; intro i _; change (V₁).coming i _ _=_; unfold coming; dsimp only; rw [h i]; exact smul_comm _ _ _
lemma vF_scaled (z:I)(χ:Chi)(V:Grid c): vF V₁ z χ V= ((µ) z) • vF Y z χ V:=by
    unfold vF; apply divideC; intro i; dsimp only; let x:= prism T τ χ o.K V (allot i); unfold Pipe.shootsP; let p:= Y.suitcase (allot i); change ite (Ac.Spark p.gP z ∧ p.born z ∧ RG.flags (Pressure.temp x.x) x.V ∩ p.full z=(roster z.toLeft).flags) _ _=((µ) z) • ite (Ac.Spark p.gP z ∧ p.born z ∧ RG.flags (Pressure.temp x.x) x.V ∩ p.full z=(roster z.toLeft).flags) _ _
    split
    swap; · exact (smul_zero _).symm
    unfold draws; apply divideC; intro i'; unfold call; rw [← integral_smul]; exact integral_congr_ae (Eventually.of_forall fun u=>capacity_scaled Y f' a h ..)
def marked_amount (z:Clusters Y.Bright):ℂ:=∏ i,(µ) (z.2 i).val
lemma furnace_scaled (z:Clusters Y.Bright)(V:Grid c): furnace V₁ χ V z=marked_amount Y a z • furnace Y χ V z:=by
    let x:= marked_amount Y a z; unfold furnace termP; rw [smul_comm (marked_amount Y a z),smul_comm (marked_amount Y a z)]; apply congr_arg; apply congr_arg; apply Eq.trans _ (prod_smul _ _ _); apply prod_congr rfl; intro i _; exact brisk_scaled Y f' a h ..
lemma honest_scaled (z:Clusters Y.Bright)(V:Grid c): honest V₁ χ V z=marked_amount Y a z • honest Y χ V z:=by
    unfold honest; rw [show GasP.seatP (V₁).lightF z= GasP.seatP Y.lightF z from rfl]; by_cases hi: Healthy (Pressure.temp τ) (seatP Y.lightF z) V
    · rw [masked_eq _ _ _ _ hi,masked_eq _ _ _ _ hi]; exact furnace_scaled Y f' a h z V
    rw [masked_ne _ _ _ _ hi,masked_ne _ _ _ _ hi,smul_zero]
open Patron Sway OrbitG
lemma crude_scaled (z:Clusters Y.Bright)(W:Clusters Y.Bright→RegularAddress c): (crude V₁ χ W).view z=marked_amount Y a z • (crude Y χ W).view z:=by
    funext U; unfold crude pepper; dsimp only [Pi.smul_apply]; rw [←integral_smul]; apply integral_congr_ae; filter_upwards with p; rw [furnace_scaled Y f' a h]; exact Subtype.ext (show _ from map_smul (Kit.disguise (rotates N p)) (marked_amount Y a z) (Y.furnace χ (Lattice.gauge p U) z).1)
open Cove.Send
open Jets.Touch
open Creek Flume Mask
open MeasureTheory
omit h
section fresh
variable {M:BudgetPoint}{b:ℝ}{H₁:Cash W τ μ L Q o C T (trimP T M δ β b)}
variable {E J D:Type} [Countable E][Countable J][Fintype D]
variable (Yp : Send S.ratio N D) (p:Rise f N E J) (g:E→Grid f→EvenA f N) (w:J→Grid f→EvenA f N)
local notation "R!"=> ({p with main:=g,plug:=w}: Rise f N E J)
local notation "I!"=> Wound (roof Yp p 30 (radiusB τ))
local notation "I?"=> (Fj D E J)
-- do not need geometry lemmas for these types, updating g,w is rfl
variable (a₀:E→ℂ) (a₁:J→ℂ)
open Cove.Fj
local notation "R'"=>deckHue H₁ Yp p (roof Yp p 30 (radiusB τ))
def Weight (z:Finset (Fj D E J)):ℂ:= (∏ i∈leftE z,a₀ i)*(∏ j∈spent z,a₁ j)
variable (ht:∀ i U, NormedSpace.exp (({p with main:=g,plug:=w}: Rise f N E J).reading M.threshold U i)-1=a₀ i • (NormedSpace.exp (p.reading M.threshold U i)-1)) (hy:∀ j U,w j U = a₁ j • p.plug j U)
include ht hy
omit [Countable E] [Countable J] [Fintype D]
lemma WaveDegree (z:Finset (Fj D E J))(U:Grid f): hue Yp ({p with main:=g,plug:=w}: Rise f N E J) M.threshold z U = Weight a₀ a₁ z • hue Yp p M.threshold z U:=by
    have h : made ({p with main:=g,plug:=w}: Rise f N E J) M.threshold U z = Weight a₀ a₁ z • made p M.threshold U z:=by
         unfold made Weight; rw [show (∏ i∈leftE z,_)= (∏ i∈leftE z, a₀ i) • ∏ i∈leftE z,(NormedSpace.exp (p.reading M.threshold U i)-1) from Eq.trans (prod_congr rfl fun i _=>ht i U) (prod_smul ..), show (∏ i∈ spent z,_)= (∏ j∈spent z,a₁ j) • ∏ j∈spent z,p.plug j U from Eq.trans (prod_congr rfl fun j _=>hy j U) (prod_smul ..)]
         exact smul_mul_smul_comm ..
    unfold hue; change ite (p.spare (spent z) ∧ closeS Yp p M.threshold z U) _ _=_; split
    swap; · exact (smul_zero _).symm
    apply Subtype.ext; change Cove.light _ (dye Yp _ M.threshold z U)=Cove.light (Keys c N) (Weight a₀ a₁ z • dye Yp p M.threshold z U); rw [map_smul,dipping,dipping,h,map_smul,map_smul,map_smul,map_smul]
lemma inkDegree (z:Wound (roof Yp p 30 (radiusB τ)))(U:Grid f)(V:Grid c): let r:= deckHue H₁ Yp ({p with main:=g,plug:=w}: Rise f N E J) (roof Yp ({p with main:=g,plug:=w}: Rise f N E J) 30 (radiusB τ)); r.works z U V=Weight a₀ a₁ z.val • (deckHue H₁ Yp p (roof Yp p 30 (radiusB τ))).works z U V:=by
      intro r; change (δ⁻¹^ (Loom.budget p z.val) • hue Yp ({p with main:=g,plug:=w}: Rise f N E J) M.threshold z.val U)=Weight a₀ a₁ z.val • ((deckHue H₁ Yp p (roof Yp p 30 (radiusB τ))).works z U V); rw [WaveDegree Yp p g w a₀ a₁ ht hy]; exact smul_comm _ _ _
end fresh
end YM.QCD.Loom.Fleet
#print axioms YM.QCD.Loom.Fleet.WaveDegree
#print axioms YM.QCD.Loom.Fleet.vF_scaled
#print axioms YM.QCD.Loom.Fleet.honest_scaled
