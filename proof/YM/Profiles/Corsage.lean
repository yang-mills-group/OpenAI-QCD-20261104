import YM.Oars.PursePages
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon Apron Apron.Grove Cupola Plate Card Iris
open MassiveQCD.Sample.LoomT Massive.Poised Massive.Poised.Plans Massive.Poised.Plans.Stamp Massive.UV Stative Massive.Poised.Pipes
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical Stamp
variable {I J E D' :Type}[Fintype I][Fintype J]
open QCD.Kites QCD.Conductor QCD.Acre QCD.Acre.Rails QCD.Struck QCD.Struck.Library Weft
variable {c f L:Side}{v t Θ Γ α β κ:ℝ}{P:BudgetPoint}{k n l m d j:ℕ}
variable (N:ℕ)(q:I→Bool)(o:I→Site c)(i:I)
namespace ProfileL
open NormedSpace
set_option quotPrecheck false
local notation "q₀"=> fun (_:Unit)=> q i
local notation "p₀"=> fun (_:Unit)=> o i
local notation "A"=> Keys c N
noncomputable def wellAt (a:I) (_:Unit): Prop:= a=i
local notation "R"=> wellAt i
lemma pledgeAt : Pledge q (q₀) (R) Set.univ Set.univ:=⟨⟨Set.mem_univ _,fun _ _ _ _=>Set.mem_univ _,fun _ _ _ _ _ _ _ _ _=> Subsingleton.elim ..⟩, fun i _ hx=>congr_arg q (show i=_ from hx),fun _ _ _=>Set.mem_univ _⟩
local notation "H"=> pledgeAt q i
local notation "G"=> Sample.flame (Keys c N) q (q₀) (findV R ({()}:Finset Unit)) (fun (_:I) (_:Unit)=>1) -- ℝ binder syntax
local notation "Xu"=> Patio (A⊕Spine I)
local notation "p!"=> burst q ({i}:Finset I)
local notation "Ω"=> burst (q₀) ({()}:Finset Unit)
variable (x:Patio (Keys c N⊕Spine I)) (hw:Polite q {i} x) (Y:Film c N I E)
include hw
lemma chosenAt : Polite (q₀) {()} (G x) ∧ pluck A Ω (G x)=pluck A p! x :=by
    have he:= edgeS (A) q (q₀) (fun (_:I) (_:Unit)=>(1:ℝ)) R H i () {()} (Set.mem_univ _) (mem_singleton_self _) (show R _ _ from rfl) x hw; simp only [Complex.ofReal_one,one_smul] at he; exact ⟨⟨_,he.symm⟩,(congr_arg (scrape _ Ω) he).trans (quid ..)⟩
omit hw
noncomputable abbrev twig := {a:E // Y.z a={i}}
local notation "Tv"=> twig N i Y -- order inspect
noncomputable def twigT: Film c N Unit Tv:= ⟨fun j=>Y.addr j.val, fun _=>{()},fun j V=>G (Y.mark j.val V)⟩
local notation "K"=>twigT N q i Y
variable (hY:Y.Beat N o q t)
include hY
set_option maxRecDepth 5000 in
set_option maxHeartbeats 640000 in
lemma bearsAt : Film.Beat N (p₀) (q₀) (K) t:=by
   let f:= G; have hm(j:Tv)(V): Polite q {i} (Y.mark j.val V):=by exact Eq.mp (congr_arg (fun s=>Polite q s (Y.mark j.val V)) j.property) (hY.budget j.val V).1
   have hp(j:Tv)(V):=(chosenAt N q i _ (hm j V)); refine ⟨fun _=>singleton_nonempty _,?_,fun j=> f.toLinearMap.toContinuousLinearMap.measurable.comp (hY.matters _),fun j V Z he hw=> congr_arg f (hY.reads j.val V Z he hw),fun j V z=> ?_,fun j V ht=>hY.mask j.val _ (fun H'=>ht ((congr_arg f H').trans (map_zero _))), fun j V=> ?_⟩
   · intro j; simp only [show (K).z j={()} from rfl,image_singleton]; exact singleton_subset_iff.mpr (hY.spark j.val (mem_image_of_mem o (Eq.mp (congr_arg (fun s : Finset I=>i∈s) j.property.symm) (mem_singleton_self i))))
   · have he:= drift q (q₀) (fun (_:I) (_:Unit)=>(1:ℝ)) R H N {i} {()} (Y.mark j.val (Lattice.gauge z V)) z (meeting R (H).mast i () (Set.mem_univ _) (show R i () from rfl)) (hm j _); exact he.trans (congr_arg f (hY.color j.val V z))
   let v := (K).mark j V; refine ⟨(hp j V).1,fun u=>?_⟩; by_cases h:u= Ω; · subst u; change pluck _ _ v∈_; rw [show pluck _ _ v= _ from (hp j V).2]; exact (hY.budget _ _).2 _
   change pluck _ _ v ∈_; rw [show pluck _ _ v=0 from (hp j V).1.spectral _ h]; exact Subalgebra.zero_mem _
open QCD.Shells.Warmlet Push.AbsoluteSums
lemma paysAt (hu:Y.Stock N k α β v κ (fun _=>1))(hy:0 ≤α)(hv:0 < v) (hb:Γ≤β) : (K).Stock N k α Γ v κ (fun _=>1):=by
   obtain ⟨g,hq,hx⟩:=hu.price; have hz(j:Tv)(V): Polite q {i} (Y.mark j.val V):=by exact Eq.mp (congr_arg (fun s=>Polite q s (Y.mark j.val V)) j.property) (hY.budget j.val V).1
   have hl(j:Tv)(V):= chosenAt N q i _ (hz j V)
   refine ⟨g ∘ Subtype.val,?_,fun e=>?_⟩
   · intro j V; let x:=Y.mark j.val V; let z:= G x; refine le_trans (?_ : Film.glyph N K V j v ≤ Film.glyph N Y V j.val v) (hq _ _); change Stitch.Tablet.credits v z ≤ Stitch.Tablet.credits v x; rw [Stitch.Tablet.polite_bill {()} _ (hl j V).1 hv, Stitch.Tablet.polite_bill {i} _ (hz j V) hv]; exact le_of_eq (congr_arg (fun x=>Creek.load (fun (_: A)=>v) x) (hl j V).2)
   · let F j:= Y.addr j |>.place; let g₀:=Film.fares N Y g (fun _=>1) α; let φ l:= if e∈F l then g₀ l*Real.exp (Γ*coverNumber k (F l)) else 0; have hZ : SumBudget φ κ :=fresh _ _ hx hb (fun j=>?_ ) e; rotate_left; · unfold Film.fares taxed; exact mul_nonneg (pow_nonneg hy _) (mul_nonneg (prod_nonneg fun i _=>abs_nonneg _) ((Creek.load_nn ..).trans (hq _ 1)))
     have hr: Summable (φ ∘ fun x:Tv=>x.val):= hZ.2.1.comp_injective Subtype.val_injective
     have hJ : SumBudget (φ ∘ (fun x:Tv=>x.val)) κ:= ⟨fun j=>hZ.1 j.val,hr,le_trans (Summable.tsum_le_tsum_of_inj (fun x:Tv=>x.val) Subtype.val_injective (fun i _=>hZ.1 i) (fun i=>le_rfl) hr hZ.2.1) hZ.2.2⟩
     convert! hJ using 1; funext i; simp only [φ,Function.comp_apply,F,twigT,g₀,Film.fares,taxed,abs_one,prod_const_one,one_mul]
end ProfileL
end YM.MassiveQCD.Sample
#print axioms YM.MassiveQCD.Sample.ProfileL.bearsAt
