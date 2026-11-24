import YM.Profiles.Posy
import YM.Profiles.Proto
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
namespace Posy
variable {Z:Type}{δ β':ℝ}
variable (q:I→Bool)(X: Reel c 6 I E)(Taper:Massive.SourceRead.TaperHol){U:Source.Hol su}(B:Massive.Lining.Temper.Collage.Exhibit U)(p:I → Cover)(x:I→ Label d)(v:I→ℝ)(Pt:BudgetPoint)
variable {u a θ y:ℝ}{L₀:ℕ}
variable (F: Patron.Rail c 6 Z)(Y:Code c 6)(z:ℂ)(V:Grid c)(K:Grid c→ℝ)(W:Run.St c)
local notation "X0"=> Keys c 6
local notation "ω"=>wrap c ∘ p
local notation "Fp"=> Y.EvalK z
local notation "Ev"=> heartS (Y.EvalE z) P.threshold K W
open NormedSpace Kites Quills
variable (G:Grid c→ Patio (Keys c 6⊕Spine I))(D:Set (Finset I))
variable {v0 v₁ w T S R δ:ℝ}{cV m₀ nL :ℕ}
variable (hY: PayLayer Taper B p q Pt Y z K W x v (l:=l) P u β' w T G D m₀ nL)
-- occupancy affordability from `Gel.May.coast` high μ. reserve exponent.Step support.Disperse
variable (hP:Pilot Taper B d Pt.order Pt.power m₀ nL l θ y) (hq:30*(l+1)≤ c.val)(hS:l+1 ≤ Pt.B)(hp:Fires (wrap c ∘ p) cV)
variable (hV:1 ≤ u)(hL:1 ≤ β')(hF:Kites.Quits (Y.EvalK z) Pt.B S v0 v₁ u) -- fix constants
variable (hW: ∀ i, Real.exp ((1/8:ℝ)*81) * y * wealth (x i).val Pt.threshold u + v i≤ R) (hr:0 ≤ R)(hx:Pt.threshold=P.threshold) (hy:‖NormedSpace.exp (heartS (Y.EvalE z) P.threshold K W V)‖ ≤ Globe.expo (-a) c) -- be careful Globe namespace.
local notation "areaC"=> (Fintype.card (Site c):ℝ)
local notation "fL"=>Stags.bonus cV Pt.B (1/32)
local notation "Φʳ"=>fL *R + w
local notation "ΦV"=>S+T
include hY hP hq hS hp hV hW hr hF hy hx hL
lemma points (f:Fin n→I)(hi: Injective f)(ht: Quills.crest f∈ D)(hz:1≤ v0)(hw:0≤v₁) : ‖(numbered q (Keys c 6) f (G V))‖ ≤ Real.exp (areaC* (a+Φʳ+ΦV)):=by
     obtain ⟨I',hI,J0,hJ,Xm,G0,hG,Kv,Tt,h1,h2,h3,h4,hZ,hWZ⟩:=hY.booth
     let E':= Gel.May.Roles q B p Pt d x l Tt Xm; let U:=relativeE 6 E' Kv Fp Ev Pt.threshold V
     have hR:pluck X0 (burst q (Quills.crest f)) (G V)= pluck X0 (burst q (Quills.crest f)) U:= (phoenixC _ _ _ _ (hWZ _ ht V) _ (Ribbon.located q _)).trans (congr_arg (fun t:ℝ=> pluck _ _ (relativeE 6 E' Kv Fp Ev t V)) hx.symm)
     change ‖signG q f • pluck X0 (burst q (Quills.crest f)) (G V)‖ ≤ _; rw [hR,norm_smul,(arm_bill q f hi).1,one_mul]
     refine (scrapeP U _).trans ?_; let X':= Stags.unionL 6 (fun i=> Stags.burstY 6 q i (ritual (Tt i)))
     have hm:= Gel.May.coast q Taper B p Pt d x l m₀ nL hP Tt v hZ hV hq _ hS hp (show Footprint.reserve (1/8) (1/32) 1 (1/32) from by norm_num [Footprint.reserve]) hW hr
     let r:= E'.rope Pt.threshold V; have h2': Xm.Occupant (wrap c ∘ p) q u Pt 2 (1/32) w (fun _=>1):=by
         obtain ⟨f,hf,hx⟩:=h2.reserve; refine ⟨h2.booked,f, QCD.Shells.Warmlet.fresh _ _ hf (by norm_num) (fun i=>?_ ),hx⟩
         obtain ⟨j,hj⟩:= h2.booked.stays i; simp only [abs_one,prod_const_one,one_mul]; exact (hx i j hj).travels
     have hV':E'.Occupant (wrap c ∘ p) q u Pt 2 (1/32) (Φʳ) (fun _=>1):= Gel.May.jointlyEarn q p Pt Xm X' h2' hm (by rw [add_comm]) -- fix
     have hr':‖r‖ ≤ areaC*Φʳ:= provision E' q ω V hV' hV (by norm_num)
     let u₀:= Ev V; let G':= Film.reports 6 Kv Fp Pt.threshold V; let x:=rootR (Spine I) (Keys c 6)
     have htV: ‖G'‖≤ Real.exp (areaC*ΦV):= filmP q ω V Kv Fp hF h4 h3 hz hL hw (by norm_num) hV -- order
     have hz': ‖x (exp u₀)‖ ≤ Real.exp (areaC*a):= (lightCost ..).trans_le (by simpa only [Globe.expo,neg_mul_neg] using hy)
     have hs : exp (x u₀+r)=x (exp u₀)*exp r:=by rw [exp_add,NormedSpace.map_exp x x.toLinearMap.toContinuousLinearMap.continuous]
     unfold U; unfold relativeE; rw [show NormedSpace.exp _= _ from hs]; apply ((norm_mul_le ..).trans (mul_le_mul ((norm_mul_le ..).trans (mul_le_mul hz' ((exp_price r).trans (Real.exp_monotone hr')) (norm_nonneg _) (Real.exp_nonneg _))) htV (norm_nonneg _) (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)))).trans; apply le_of_eq; rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
end Posy
end YM.MassiveQCD.Sample
#print axioms YM.MassiveQCD.Sample.Posy.points
