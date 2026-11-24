import YM.QCD.Villa.Pledge
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Villa
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees Beam Cove Leaf Lat Creek Loom
open Leaf Jets Fj Further.ShellBirth49.Fusing Collide Jets.Touch Fleet
open Kit Fork Port Flume YM.Next.Free Leaf Tee Orbit Quarry Garden Footprint Bay Run Jets.Sun Pine Grass Sway OrbitG
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f:Side}{P:Teller su}{δ β b τ μ W C:ℝ}{Q:Target su P}{o :Target.Order su W}{R:BudgetPoint}{N m l n i j k:ℕ}
variable {Y:StepData c f} {η p h z a a' t v u u' q:ℝ} {D E J:Type}[Countable E][Countable J][Fintype D]
variable {T : Tube su Y} {W' :ℕ→Atom su 2} {P':Plan k} {L:Side}
variable (H:Cash W τ μ L Q o C T (trimP T R δ β b))
open AnalyticBridge.GaussianFieldAlignment Locations Channels PhysicalNext.Repeat.Turn Next.Fluctuations Next.SectorChange
local notation "B" => radiusB τ
local notation "π'"=> trimP T R δ β b
variable (O:Send Y.ratio N D)(A:Rise f N E J){X: Fj D E J→Support c}
variable {s:Signed}{x:Site c}{p:OrbitG (Modes f N⊕Modes c N)}{u:OrbitG (Modes f N)}{q:OrbitG (Modes c N)} {e:Equiv.Perm E}{j': Equiv.Perm J}{d:Equiv.Perm D}
local notation "fT"=> sail d e j'
local notation "rf"=> StepData.sendSites s (Y.ratio.embed x)
local notation "rs"=> StepData.sendSites s x
local notation "tR"=> R.threshold
local notation "P'"=> deckHue H O A (roof O A 30 B)
lemma pureP (h:∀ i:Grid f,Usher Y.ratio O (pull s (Y.ratio.embed x) i) i p u q rf d)(hv:∀ U:Grid f,Parade (pull s (Y.ratio.embed x) U) U u A rf e j' tR)(π:(trimP T R δ β b).activities.Moves s (Y.ratio.embed x))(hp:∀ y:Site f,π.kp (mac y)= mac (rf y)):
     ∃ w, (deckHue H O A (roof O A 30 (radiusB τ))).Marches π w q.passL:=by
   let Z:=roof O A 30 B; let f₀ :=fT; let D':= deckHue H O A Z
   let e':=(fT).finsetCongr
   have he' i: e' i = i.image f₀:=Finset.map_eq_image ..
   have he i: Z (f₀ i)=(Z i).image rs:= PhysicalNext.Repeat.Turn.enlarged _ _ _ _ _ _ (Sway.brim_N (h 1) (hv 1) i) -- check
   have hq (i):Collide.spark Z i↔ Collide.spark Z (e' i):=PhysicalNext.Repeat.Turn.seam f₀ rs (fun i=> (display rs _ _).1 (he i)) ((given _ _ _).1 rfl) -- definitional Ac
   let w:= Equiv.subtypeEquiv   e' hq
   have hR i: D'.ground (w i)=(D'.ground i).image rs:= PhysicalNext.Repeat.Turn.gains f₀ rs (fun i=> (display rs _ _).1 (he i)) ((given _ _ _).1 rfl)
   have ht i : A.wish (spent ((w i).val))=(A.wish (spent i.val)).image rf:=by
      change A.wish (spent (e' i.val))=_; rw [he',(parts_map ..).2.2]; apply invacu (hv 1)
   refine ⟨w,phare _,?_, fun i=> (display rs _ _).1 (hR i), ?_, fun i j=> assign_guard rs ((display rs _ _).1 (hR i)) ((display rs _ _).1 (hR j)),?_⟩
   · intro i j; refine (display π.kp _ _).1 ?_ j; change _= (typo _).image π.kp -- refine goal all implicit j
     change typo (A.wish (spent (w i).val))= _; rw [ht]; unfold typo; simp_rw [image_image]; exact image_congr fun z _=> (hp z).symm
   · intro i; apply (display rs _ _).1; change radio _ _ (e' _)= (radio _ _ i.val).image _
     rw [he']; unfold radio petal; rw [bulge (h 1) (hv 1)]; change (inspected ((brimW O A i.val).image (affine s (Y.ratio.embed x)))).image Y.ratio.parent=_
     rw [Further.ThresholdSourceRestart.Sluice.Menu.looks]; exact (parent_image (Y:=Y) ..).symm
   intro i U V; change δ⁻¹ ^ budget A (w i).val • _ = q.passL (δ⁻¹ ^ budget A i.val • hue _ _ _ _ _); unfold budget; rw [ht,Finset.card_image_of_injective _ (rf).injective, eSM _ (phare _), Sway.hatch (h U) (hv U)]; exact congr_arg (δ⁻¹ ^ (A.wish (spent i.val)).card • hue O A tR · U) (he' _)
lemma gaugeP (z:Site c→su.El)(h:∀ U:Grid f,Usher Y.ratio O (gauge (constantGauge z Y.ratio) U) U p u q (Equiv.refl _) (Equiv.refl _))(hv:∀ U:Grid f,Parade (gauge (constantGauge z Y.ratio) U) U u A (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) tR) : (deckHue H O A X).sings z q.passL:=by
    refine ⟨phare _,fun i U V=>?_⟩; change q.passL (δ⁻¹ ^ _ • hue ..)= δ⁻¹ ^ _ • _; rw [Fleet.eSM _ (phare _),Sway.hatch (h U) (hv U)]; simp [Sway.sail]
lemma hue_voice (h:A.Wave tR): (deckHue H O A X).speaking:=by
   intro i; have ht: Measurable (hue O A _ _):= rigid (morals O A tR h i.val); exact measurable_const.smul (ht.comp measurable_fst)
end YM.QCD.Villa
