import YM.QCD.Villa.Olive
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
open Extra Sway OrbitG Bay Strut Revolve
local notation "S"=>Y.ratio
variable {O:Flight j k}{d:f.val=c.val*O.L.val} {W':ℕ→Atom su 2}{W'':Grid f→Sheet f}
variable (Z:Swathe O d W'' W' P' u v η p a i)
local notation "Z'"=>VarnC H Z N
lemma cycles (hx:Y.ratio=sliceL O d)(t:Signed)(q:Site c)(g:Site c→ℂ)(p':Spike) {g':Site f →ℂ}(hv:Warrant (raise Y.ratio (t,q)) g' p')(hg:g=g' ∘ Y.ratio.embed)(π:(trimP T R δ β b).activities.Moves t (Y.ratio.embed q)):
    (Z').Marches π (tagJump Y.ratio (t,q)) (trade (copies N (haze (t,q) p' g))).passL:=by
   let V:=tagJump Y.ratio (t,q); let u:=StepData.sendSites t q
   have h a: vap (V a) Y.ratio B=(vap a Y.ratio B).image (affine t q):=by unfold vap; rw [← Port.pump a]; change halo _ (((payT Y.ratio B a).image (affine t (Y.ratio.embed q))).image Y.ratio.parent)=_; rw [← parent_image, halo_image]
   refine ⟨phare _,fun i j=> iff_of_false (Finset.notMem_empty _) (Finset.notMem_empty _),fun i=> (display u _ _).1 (show halo _ (vap _ _ _) = _ from ?_),fun i=> (display u _ _).1 (h i),fun _ _=> Iff.rfl,fun i U V=>?_⟩
   · change halo (30*radiusB τ) (vap (V i) Y.ratio B)=(halo (30*radiusB τ) (vap i Y.ratio B)).image (affine t q); rw [h,halo_image]
   let Q:= (trade (copies N (haze (t,q) p' g)))
   apply Eq.symm
   change Q.passL (broke Z ..) = broke Z ..
   have hf: raise (S) (t,q)=raise (sliceL O d) (t,q):=by rw [hx]
   unfold broke; rw [map_sub,map_one,NormedSpace.map_exp Q.passL Q.phare]
   apply congr_arg₂ (·-·) _ rfl; apply congr_arg
   unfold Q; rw [hg,hx]; rw [hf] at hv; exact royalties Z N i B U (s:=(t,q)) hv
lemma varnV (hr:0<v): (Z').speaking:=by
    intro i; have hF: Continuous (broke Z N B i):= (NormedSpace.exp_continuous.comp (Port.forestV Z hr ..)).sub continuous_const; exact hF.measurable.comp measurable_fst
lemma boon (W:OrbitG (Modes c N))(x:Site c→su.El)(hp:∀ i U,W.passL (sliceF Z N B i (Lattice.gauge (constantGauge x Y.ratio) U))=sliceF Z N B i U) : (VarnC H Z N).sings x W.passL:=by
    refine ⟨phare _,fun i U V=>?_⟩; change W.passL (NormedSpace.exp (sliceF _ _ _ _ _)-1)= NormedSpace.exp _-1; rw [map_sub,map_one,NormedSpace.map_exp W.passL W.phare,hp]
-- output ROOT scholar is also symmetric at purchase same
variable {D₁ σ:ℝ}{Jx:Train k}
local notation "G"=>singleR c
def Torch (Γ:Land c (Site c) (Site c)):Prop:= Held (singleR c) (sun (singleR c)) (sun (singleR c)) Γ ∧ seed Γ=Γ
open scoped Matrix
lemma candor (X: Heritage (id:Site c→Site c) id σ τ l (wood P' (0:Site c) Jx) D₁) : ∃ Γ Y, Run.Pack id id σ τ l (wood P' (0:Site c) Jx) D₁ Γ Y ∧ Torch Γ :=by
   obtain ⟨Γ,D,h⟩:=X
   have ht: Tow (singleR c) (sun G) (sun G) (wood P' 0 Jx) := ⟨fun p g T U hh=> spin_wood hh.1 hh.2 Jx P' U⟩
   obtain ⟨Γ,Y,h,hQ⟩:=honors h ht
   have hh:(fun U:Grid c=> foldH (wood P' 0 Jx U)) = wood P' 0 Jx:=by
     funext U; let X:= wood P' (0:Site c) Jx U; change chirality c*Xᴴ*chirality c=X; nth_rw 2 [← chi_star (n:=c)]; exact (funds0 _).2 (show QCD.Cost.Chiral _ X from spinO ..)
   obtain ⟨Γ,D',h,hV,hL⟩:=carry h hQ hh; exact ⟨Γ,D',h,hV,hL⟩
end YM.QCD.Villa
