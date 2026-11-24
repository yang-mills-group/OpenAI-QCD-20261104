import YM.Oars.Banners
/-!
 # Input/output endpoint for Mesh.Frame. Budget energies grant proper positivity for coordinate U.Test, and identify body.Volume globally.
 -/
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
variable (X:Massive.SourceRead.TaperHol){U:YM.Source.Hol su}(B:Massive.Lining.Temper.Collage.Exhibit U)(o:I → Cover)(q:I→Bool)(p:BudgetPoint)
variable (A:Code c 6)(z:ℂ)(F:Grid c→ℝ)(S:QCD.Run.St c)
local notation "αC"=> (1/8:ℝ)
local notation "μτ"=> (40/256:ℝ)
local notation "Wr"=>wrap c ∘ o
variable (ψ:I→Massive.UV.Label d)(w:I→ℝ)(Φ:Grid c→EvenA c (ample 6 I))
namespace PayLayer
variable (Z:Grid c→Patio (Keys c 6⊕Spine I))(H:Set (Finset I))
variable (h:PayLayer X B o q p A z F S ψ w (l:=l) P v α β κ Z H k n)
local notation "XΓ"=>Keys c 6
local notation "EΓ"=> heartS (A.EvalE z) P.threshold F S
local notation "KΓ"=> A.EvalK z
local notation "ΩΓ"=> Cove.light (Keys c 6) ∘ (Maternal A P F S z)
variable (hv:1≤v)(ht:p.threshold=P.threshold)
variable (hq:1≤α)(hF:∀ V,Summable fun i=>‖(A.EvalK z).warp i V‖)
-- need film summable generic lemma
lemma freshT {μ A:ℝ} (Y:Film c 6 I E)(U:Grid c)(P:BudgetPoint)(hm:1 ≤ v)(hα:1 ≤ t)(hx:0 ≤ μ) (ht:Y.Stock 6 P.B t μ v A (fun _=>1))(hv: Y.Beat 6 (wrap c ∘ o) q P.threshold): Summable fun i=>‖Y.mark i U‖:=by
    obtain ⟨f,hf,h⟩:=ht.price; let S i:=Y.addr i |>.place
    choose δ hδ using hv.commits; let r:=fun i=>‖Y.mark i U‖; have hP i:r i≤ f i:= (loaded (Y.mark i U).val (Stitch.Tablet.chip v XΓ (Spine I)) (fun j=>by rcases j with j|j; exact hm; exact le_rfl)).trans (hf ..)
    let g(j:I)i:= if (Wr) j ∈ S i then Film.fares 6 Y f (fun _=>1) t i*Real.exp (μ*coverNumber P.B (S i)) else 0; let u i:= ∑ j:I,g j i; apply (show Summable u from summable_sum (s:=Finset.univ) fun j _=> (h _).2.1).of_nonneg_of_le (fun i=>norm_nonneg _) fun i=> ?_
    apply le_trans (hP i); refine le_trans ?_ (single_le_sum (f:=fun j:I=>g j i) (fun j _=>(h (wrap c (o j))).1 i) (mem_univ (δ i))); unfold g; rw [if_pos (show _ from (show (Wr) (δ i)∈ S i from hv.spark i (mem_image_of_mem _ (hδ i))))]; have hy:0≤f i:=(show 0≤r i from norm_nonneg _).trans (hP i); unfold Film.fares taxed; simp only [abs_one,prod_const_one,one_mul]; exact (le_mul_of_one_le_left hy (one_le_pow₀ hα)).trans (le_mul_of_one_le_right (by positivity) (Real.one_le_exp (mul_nonneg hx (Nat.cast_nonneg _)))) -- Kred. shadow
include h hv ht hq hF
variable (hP0: Pilot X B d p.order p.power k n l Θ Γ) (hz:30*(l+1) ≤ c.val)
include hP0 hz
lemma vacuumR (i: Finset I)(hi:i∈H) (V:Grid c) : pluck (Keys c 6) ∅ (Z V)= (ΩΓ V) :=by
    obtain ⟨I,hI,J0,hJ,Y,G,HG,R,T,h1,h2,h3,h4,hZ,hW⟩:=h.booth
    let f:= Gel.May.Roles q B o p d ψ l T Y; have hp: Reel.Book Wr q f:=by
        apply Gel.May.jointly q o Y _ h2.booked; exact Stags.gatherings 6 (wrap c ∘ o) q _ (fun i=> Stags.burstP 6 Wr q _ _ (rendition hP0 rfl rfl hv hz _ (hZ i)|>.1))
    have hP(V) :Summable (fun i=> Reel.mist f P.threshold i V):=by
        obtain ⟨g,hO,hΨ⟩:= h2.reserve; simp only [abs_one,prod_const_one,one_mul] at hO
        rw [← ht]; exact Summable.sum _ (creditE (wrap c ∘ o) q Y _ h2.booked hΨ hO (by norm_num) hv V) (Gel.May.surf q X B o p _ ψ l k n hP0 T w hZ hv hz _ (by norm_num))
    refine (phoenixC _ _ _ i (hW i hi V) ∅ (by simp)).trans (atom_zero 6 q Wr V f R KΓ P.threshold EΓ hp (ht ▸ h3) hP (fun i=> freshT o q R i p hv hq (by norm_num) h4 h3) hF) -- order p vs q
end PayLayer
end YM.MassiveQCD.Sample
#print axioms YM.MassiveQCD.Sample.PayLayer.vacuumR
