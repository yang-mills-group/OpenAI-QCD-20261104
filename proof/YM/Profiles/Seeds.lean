import YM.Profiles.Sparkle
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
local notation "R"=> wellAt i
local notation "H"=> pledgeAt q i
local notation "G"=> Sample.flame (Keys c N) q (q₀) (findV R ({()}:Finset Unit)) (fun (_:I) (_:Unit)=>1) -- ℝ binder syntax
local notation "Xu"=> Patio (A⊕Spine I)
local notation "p!"=> burst q ({i}:Finset I)
local notation "Ω"=> burst (q₀) ({()}:Finset Unit)

-- exact motion up to this aperture. No expectation used
local notation "Fx"=> fun (_:I) (_:Unit)=> (1:ℝ)
local notation "Tx"=> findV R ({()}:Finset Unit)
local notation "Zh"=> Patio (A⊕Spine Unit)
local notation "GD"=>Stags.amber (c:=c) N q i
open Card.Iris Puff Stags
lemma boughtBack (u:Patio (A⊕Spine Unit))(hp:Polite (fun _:Unit=> q i) topM u): G (GD u)=u:=by
    have ht:= goldPay N q i u hp; have hw:= chosenAt N q i _ ht.1; apply pluckVisible; intro j; by_cases he:j= Ω; · subst j; exact hw.2.trans ht.2
    rw [show pluck _ _ _=0 from hw.1.spectral j he]; exact (hp.spectral _ he).symm
open Reel
variable (Y: Reel c N I E)(Q:Puff c N D' (q i))(U:Grid c)
lemma leafless (hy:Reel.Book o q Y)(hE:∀ i, 2 ≤ (Y.z i).card) (hK:Summable fun j=>Reel.mist Y t j U) : G (Reel.rope Y t U)=0:=by
    apply Eq.trans ((G).toLinearMap.toContinuousLinearMap.map_tsum hK); refine (tsum_congr (g:=fun _=> (0:Zh)) ?_).trans tsum_zero; intro k; unfold Reel.mist; by_cases H':Healthy t (Y.addr k).support U; · rw [masked_eq _ _ _ _ H']; apply extinct N q i (Y.z k) (Y.mark k U) (hy.stage k U).1 (hy.stays k); intro h; have hx:= hE k; rw [h,card_singleton] at hx; omega
    rw [masked_ne _ _ _ _ H']; exact map_zero _
lemma burstStirs (u:I)(Q: Puff c N E (q u))(he:Summable fun a=> Reel.mist (Puff.roll N Q) t a U) : Reel.rope (burstY N q u Q) t U= amber N q u (Reel.rope (Puff.roll N Q) t U):=by
    let Z:=burstY N q u Q; let X:=Puff.roll N Q; let g:= (Stags.amber (c:=c) N q u); apply Eq.trans _ ((g.toLinearMap.toContinuousLinearMap.map_tsum he).symm); apply tsum_congr; intro j; unfold Reel.mist
    by_cases H':Healthy t (Q.addr j).support U; · rw [masked_eq _ _ _ _ (show Healthy _ (Z.addr _).support _ from H'),masked_eq _ _ _ _ (show Healthy _ (X.addr _).support _ from H')]; rfl
    rw [masked_ne _ _ _ _ (show ¬ Healthy _ (Z.addr _).support _ from H'),masked_ne _ _ _ _ (show ¬Healthy _ (X.addr _).support _ from H')]; exact (map_zero _).symm
lemma feather {u:I} (Q:Puff c N D' (q u)) (V:Grid c)(hp:Summable fun i=> Reel.mist (Puff.roll N Q) t i V) : Polite q {u} (Reel.rope (burstY N q u Q) t V):=by
    rw [burstStirs _ q V _ _ hp]; have he: Polite (fun _ : Unit=> q u) topM (Reel.rope (Puff.roll N Q) t V):= polite_tsum (fun i=> by unfold Reel.mist; by_cases H': Healthy t (Q.addr i).support V; rw [masked_eq _ _ _ _ (show Healthy _ ((Puff.roll N Q).addr _).support _ from H')]; exact worthE N _ _ (Q.beams i) V; rw [masked_ne _ _ _ _ (show ¬ Healthy _ ((Puff.roll N Q).addr _).support _ from H')]; exact polite_nil ..)
    exact (goldPay N q u _ he).1
-- marked ledger Scope. pass into Medicaid ingredients.P altitude and Cost. µ normalized earlier.
end ProfileL
end YM.MassiveQCD.Sample
#print axioms YM.MassiveQCD.Sample.ProfileL.feather
