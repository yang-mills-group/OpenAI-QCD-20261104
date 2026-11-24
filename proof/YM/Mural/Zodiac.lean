import YM.Mural.Cot
import YM.QCD.Villa.Music
import YM.Mural.Canon
/-! # Support at a block matrix sweep. Uses only color-trivial condition at roots for each slot individually. Global angular change licensed by multilinear dimensions. -/
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
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{δ β τ μ W C:ℝ} {R:Rep su f}{F Z:Tree.Forest S.ratio}{Q:Target su P}{o :Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι I:Type}{N M:ℕ}
open Art Hues
open MassiveQCD.PaletteT
local notation "C'"=>Coat T
variable [Fintype I]
local notation "FI"=>Option I
local notation "I'"=> Pipe.Clump S ι
variable (Y:Fleet H ι N) (Γ:Option I→ ι→Grid f→ Grid c→EvenA c M)(T0: Site c→ su.El)
local notation "P'"=> EvenA c M
-- arbitrary Gear ℂ, closed.
structure Kit (X: Submodule ℂ (Option I→ EvenA c M)) (κ:Delta I) (g: EvenA c M →ₐ[ℂ] EvenA c M):Prop where
   earns i: (align Y (Γ i)).Famous
   tide : straight κ
   colored i U V: Binds κ g (fun j=> Γ j i (gauge (constantGauge T0 S.ratio) U) (gauge T0 V)) (fun j=> Γ j i U V)
   hale i U V: (fun j=> Γ j i U V)∈X
   origin : 1∈ X
   product f h (hf:f ∈ X)(hh:h∈X): f*h∈X
   conductor (u v:Option I→ EvenA c M)(hu:u∈X)(hv:v∈X)(i j): (u i-u none)*(v j-v none)=0
variable {Wc:Submodule ℂ (Option I→ EvenA c M)}{κ:Delta I}{g:EvenA c M→ₐ[ℂ]EvenA c M}
variable (h:Kit Y Γ T0 Wc κ g)
local notation "U" j'=> align Y (Γ j')
include h
lemma listH (X:C' F)(s:I')(k:Finset ℕ)(w:Air f su) : (fun j'=> ((U j').suitcase F).capacityP s k X w)∈ Wc:=by
    have hp(j): (fun i=> (U i).coming j X w)∈Wc.restrictScalars ℝ:= (Wc.restrictScalars ℝ).smul_mem (Y.riseP X w j) (h.hale j _ _)
    have hS:= gatheredX Wc (fun j i=> (U i).coming j X w) s.toRight (fun i _=> hp i) h.origin (fun i hi j hj=> h.product i j hi hj)
    unfold Beam.Pipe.capacityP; exact (Wc.restrictScalars ℝ).smul_mem _ hS
lemma rhymes (X:C' F)(s:I')(k:Finset ℕ)(he:X.x=τ)(ht:X.width=o.K)(hv:X.manifest)(w:Air f su):
    Binds κ g (fun j=> ((U j).suitcase F).capacityP s k (Hues.sluice X T0) (weep X T0 w)) (fun j=> ((U j).suitcase F).capacityP s k X w):=by
    have hf:ShellAccess S su X.x W X.width o.γ:= by rw [he,ht]; exact H.laws.data.access
    let V:=Hues.sluice X T0; let R':=weep X T0 w
    have hz(j:ι): ((U none).riseP V R' j)=(Y.riseP X w j):=by unfold riseP; rw [Hues.fullA _ _ H.laws.intake.ready hf]; exact Hues.mandate X T0 (2*o.a) _ (X.plaza (Y.window j))
    have hs(u v:Option I→EvenA c M)(r:ℝ)(hv:Binds κ g u v):Binds κ g (r • u) (r • v):=by rw [← Complex.coe_smul r,← Complex.coe_smul r]; exact binds_pin κ g 0 u v hv _
    have hS i:Binds κ g (fun j=>(U j).coming i V R') (fun j=>(U j).coming i X w):=by
       let F' j:= Γ j i (X.input (X.liftA R.beta w)) X.V
       let F'' j:= Γ j i (V.input (V.liftA R.beta R')) V.V
       have hf': V.input (V.liftA R.beta R')=gauge (constantGauge T0 S.ratio) (X.input (X.liftA R.beta w)):=by unfold V R'; rw [Hues.fullA _ _ H.laws.intake.ready hf,banks]
       have hh: Binds κ g F'' F' :=by unfold F''; rw[hf']; exact h.colored i _ _ -- binder
       change Binds κ g ( ((U none).riseP V R' i) • F'') ( (Y.riseP X w i) • F'); rw [hz]; exact hs _ _ _ hh
    have hl i: (fun j=> (U j).coming i X w)∈Wc.restrictScalars ℝ:= (Wc.restrictScalars ℝ).smul_mem (Y.riseP X w i) (h.hale i _ _)
    have hh:= binds_prod κ g Wc h.origin (fun i hi j hj=>h.product i j hi hj) (fun i hi j hj=>(h.conductor i j hi hj)) (fun i j=> (U j).coming i V R') (fun i j=> (U j).coming i X w) s.toRight (fun i _=> hl i) (fun i _=>hS i) h.tide
    unfold Pipe.capacityP; let Q i:= ((U i).suitcase F).averageP s.toRight V R'; let X' i:=((U i).suitcase F).averageP s.toRight X w
    unfold Coat.term; rw [show (∏ i∈s.toLeft,_)=_ from prod_congr rfl fun i _=> H.scours X he ht hv k T0 w i]; exact hs Q X' _ hh
-- align uses capacity shape (unmatched funcs); output observes left read orientation.
lemma aspirates (X:C' F)(u:I')(hx:X.x=τ)(ht:X.width=o.K): (fun i=>((U i).suitcase F).shootsP X u)∈Wc:=by
    unfold Pipe.shootsP; simp_rw [show ∀ i, ((U i).suitcase F).born u=(Y.suitcase F).born u from fun _=> rfl,show ∀ i, ((U i).suitcase F).gP=(Y.suitcase F).gP from fun _=>rfl,show ∀ i, ((U i).suitcase F).full=(Y.suitcase F).full from fun _=>rfl]; split; swap; · exact Wc.zero_mem
    let A:= Matter.planted X u.toLeft; let k:=Matter.own u.toLeft
    unfold Beam.draws choiceS; refine (Wc.restrictScalars ℝ).smul_mem (((Fintype.card S.Choices:ℝ))⁻¹) (show _∈Wc from shines Wc (fun j i=>call (A.taggedL j) (((U i).suitcase F).capacityP u k)) _ (fun j _=>?_)); let J:= A.taggedL j
    exact entered Wc (μ:=(F.order su).prod J.dice) (fun i p=>((U i).suitcase F).capacityP u k (J.wrapY p.1) p.2) (fun i=>envPlot (((U i).suitcase F).ripeP k u (Fleet.forwarded _ _ (h.earns i)) J hx ht (planted_valid X _)) _) (fun p=>listH Y Γ T0 h _ _ _ _)
lemma blasts (X:C' F)(u:I')(hx:X.x=τ)(ht:X.width=o.K): Binds κ g (fun i=>((U i).suitcase F).shootsP (X.rinse T0) u) (fun i=>((U i).suitcase F).shootsP X u):=by
   let A:= Matter.planted X u.toLeft; let k:= Matter.own u.toLeft
   let R' i:= ((U i).suitcase F).capacityP u k
   unfold Pipe.shootsP; rw [show (X.rinse T0).x=X.x from rfl,show (X.rinse T0).V=gauge T0 X.V from rfl,gauge_flags]; simp_rw [show ∀ i, ((U i).suitcase F).born u=(Y.suitcase F).born u from fun _=>rfl,show ∀ i, ((U i).suitcase F).gP=(Y.suitcase F).gP from fun _=>rfl,show ∀ i, ((U i).suitcase F).full=(Y.suitcase F).full from fun _=>rfl]; split
   swap; · exact unity κ g h.tide 0 0 (map_zero _)
   next hk=>
    have hv : Matter.planted (X.rinse T0) u.toLeft = A.rinse T0:= by unfold A Matter.planted rinse preps; simp only [gauge_flags]
    rw [hv]; unfold draws choiceS
    have hp(i:S.Choices): Binds κ g (fun j=> call ((A.rinse T0).taggedL i) (R' j)) (fun j=>call (A.taggedL i) (R' j)):=by
      let Z':=A.taggedL i; let W':= (A.rinse T0).taggedL i; let Y':= Hues.sluice Z' T0; have hz:=H.laws.data
      have hn: Z'.manifest:= Matter.planted_valid X u.toLeft; have hM:Y'.manifest:=Cash.wind Z' T0 hn
      let P j (v:F.Slice su × Air f su) := R' j (Y'.wrapY v.1) v.2; let Q j (v:F.Slice su ×Air f su):= R' j (Z'.wrapY v.1) v.2; have hg j:= ((U j).suitcase F).ripeP k u (Fleet.forwarded _ _ (h.earns j)) Y' hx ht hM; have ht' j:= ((U j).suitcase F).ripeP k u (Fleet.forwarded _ _ (h.earns j)) Z' hx ht hn
      have hv : MeasurePreserving (fun v:F.Slice su×Air f su=> (Hues.pairs Z' T0 v.1, weep Z' T0 v.2)) ((F.order su).prod Z'.dice) ((F.order su).prod Y'.dice) := (Hues.drinking Z' T0).prod (Hues.speeds Z' T0 H.laws.intake.ready (hz.localP F Z' hx ht hn).sails.fullC (hz.localP F Y' hx ht hM).sails.fullC)
      exact seen P _ Q κ g hv (fun i=>(hg i).1) (fun i=> envPlot (hg i) _) (fun i=> envPlot (ht' i) _) (fun v=>rhymes Y Γ T0 h (Z'.wrapY v.1) u k hx ht hn v.2)
    simp_rw [← Complex.coe_smul ((Fintype.card S.Choices:ℝ)⁻¹)]; exact binds_pin κ g 0 _ _ (binds_sum κ g univ _ _ (fun i _=>hp i)) _
end YM.QCD.Loom.Fleet.Palette
#print axioms YM.QCD.Loom.Fleet.Palette.blasts
#print axioms YM.QCD.Loom.Fleet.Palette.aspirates
