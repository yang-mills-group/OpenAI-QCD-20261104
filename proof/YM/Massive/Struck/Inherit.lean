import YM.QCD.Villa.Glow
import YM.Massive.Struck.Fred
/-! # Inherit the tags selected at ticket input. Adapted from Villa Glow, Olive. Need actual port for all re-stenciled λ values at same normalized trajectory. -/
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
open Struck
def taxes (t₁:E→Dye)(t₂:J→Dye)(x:Finset (Fj D E J)): Dye :=(∑ i∈leftE x,t₁ i)+(∑ i∈spent x,t₂ i)
omit [Countable E] [Countable J] [Fintype D] in
lemma AshTax (T: Finset (Fj D E J))(t₁:E→Dye)(t₂:J→Dye) (h:∀ i,Ash (t₁ i))(hp:∀ i,Ash (t₂ i)): Ash (taxes t₁ t₂ T):=brightAdd _ _ (bright_sum _ _ fun i _=>h i) (bright_sum _ _ fun i _=>hp i)
variable (t₁:E→Dye)(t₂:J→Dye)
omit [Fintype D] in
lemma purposed (h:∀ i:Grid f,Usher Y.ratio O (pull s (Y.ratio.embed x) i) i p u q rf d)(hv:∀ U:Grid f,Parade (pull s (Y.ratio.embed x) U) U u A rf e j' tR)(ha:∀ i,t₁ (e i)=t₁ i)(hb:∀ i,t₂ (j' i)=t₂ i)(π:(trimP T R δ β b).activities.Moves s (Y.ratio.embed x))(hp:∀ y:Site f,π.kp (mac y)= mac (rf y)):
     ∃ w, (deckHue H O A (roof O A 30 (radiusB τ))).Marches π w q.passL ∧ ∀ i,taxes t₁ t₂ (w i).val=taxes t₁ t₂ i.val:=by
   let Z:=roof O A 30 B; let f₀ :=fT; let D':= deckHue H O A Z
   let e':=(fT).finsetCongr
   have he' i: e' i = i.image f₀:=Finset.map_eq_image ..
   have he i: Z (f₀ i)=(Z i).image rs:= PhysicalNext.Repeat.Turn.enlarged _ _ _ _ _ _ (Sway.brim_N (h 1) (hv 1) i) -- check
   have hq (i):Collide.spark Z i↔ Collide.spark Z (e' i):=PhysicalNext.Repeat.Turn.seam f₀ rs (fun i=> (display rs _ _).1 (he i)) ((given _ _ _).1 rfl) -- definitional Ac
   let w:= Equiv.subtypeEquiv   e' hq
   have hR i: D'.ground (w i)=(D'.ground i).image rs:= PhysicalNext.Repeat.Turn.gains f₀ rs (fun i=> (display rs _ _).1 (he i)) ((given _ _ _).1 rfl)
   have ht i : A.wish (spent ((w i).val))=(A.wish (spent i.val)).image rf:=by
      change A.wish (spent (e' i.val))=_; rw [he',(parts_map ..).2.2]; apply invacu (hv 1)
   refine ⟨w,⟨phare _,?_, fun i=> (display rs _ _).1 (hR i), ?_, fun i j=> assign_guard rs ((display rs _ _).1 (hR i)) ((display rs _ _).1 (hR j)),?_⟩, ?weight⟩
   · intro i j; refine (display π.kp _ _).1 ?_ j; change _= (typo _).image π.kp -- refine goal all implicit j
     change typo (A.wish (spent (w i).val))= _; rw [ht]; unfold typo; simp_rw [image_image]; exact image_congr fun z _=> (hp z).symm
   · intro i; apply (display rs _ _).1; change radio _ _ (e' _)= (radio _ _ i.val).image _
     rw [he']; unfold radio petal; rw [bulge (h 1) (hv 1)]; change (inspected ((brimW O A i.val).image (affine s (Y.ratio.embed x)))).image Y.ratio.parent=_
     rw [Further.ThresholdSourceRestart.Sluice.Menu.looks]; exact (parent_image (Y:=Y) ..).symm
   case weight=>
      intro i
      change taxes t₁ t₂ (e' i.val)=_
      unfold taxes; rw [he',(parts_map ..).2.1,(parts_map ..).2.2, Finset.sum_image e.injective.injOn,Finset.sum_image j'.injective.injOn]; exact congr_arg₂ _ (sum_congr rfl fun i _=>ha i) (sum_congr rfl fun i _=>hb i)

   intro i U V; change δ⁻¹ ^ budget A (w i).val • _ = q.passL (δ⁻¹ ^ budget A i.val • hue _ _ _ _ _); unfold budget; rw [ht,Finset.card_image_of_injective _ (rf).injective, eSM _ (phare _), Sway.hatch (h U) (hv U)]; exact congr_arg (δ⁻¹ ^ (A.wish (spent i.val)).card • hue O A tR · U) (he' _)

end YM.QCD.Villa

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
open AnalyticBridge.GaussianFieldAlignment Locations Channels PhysicalNext.Repeat.Turn Next.Fluctuations Next.SectorChange
local notation "B" => radiusB τ
open Sway OrbitG Strut Revolve
variable {W' :ℕ→Atom su 2}{J':Plan k}
variable (O:Flight j k)(K: KernelChoices)(d:f.val=c.val*O.L.val)
set_option quotPrecheck false
local notation "S"=> (O.visit K d).ratio
variable {T : Tube su (O.visit K d)}
variable {X:Grid f→Sheet f} (H:Cash W τ μ O.L Q o C T (trimP T R δ β b))(G:Sun O c f d η h z a a' m X) (U :Swathe O d X W' J' h η a u v i)
variable {Γ: Land c (Site c) (Site c)}{D':Pays c (Site c) (Site c)}
variable (Y': Rise f N E J)
local notation "X'"=> tableau O d K Y' H G U Γ
open Struck Patron
def rungC (e:E→Dye)(k:J→Dye): Wound (roof (G.equip N B) Y' 30 B) ⊕ Varn f c ⊕ Gaze c→ Dye:= Sum.elim (fun i=> taxes e k i.val) (fun _=>0)
omit [Countable E] [Countable J] in
lemma AshR (e:E→Dye)(k:J→Dye) (h:∀ i, Ash (e i))(he:∀ i,Ash (k i)): ∀ x,Ash (rungC O d G Y' (τ:=τ) e k x):=by rintro (i|i); exact AshTax i.val _ _ h he; exact Or.inl rfl
-- for real enhanced inputs (unit marker € and L1). `counted` permutation law
structure PantryX (f:Side)(N:ℕ)(t:ℝ)(e:E→Dye)(k:J→Dye) (X:Rise f N E J) :Prop where
 frame : X.Reframe
 turns (v:Strut f)(g:Site f→ℂ)(V:Spike): Warrant v g V → ∃ (f:Equiv.Perm E) (j:Equiv.Perm J),(∀ i,e (f i)=e i) ∧ (∀ i,k (j i)=k i) ∧ ∀ U,Parade (Strut.sky v U) U (trade (Lat.copies N (Strut.haze v V g))) X (Strut.act v) f j t -- binder f accidental rename.
 real : ∀ U, Parade U U (dawn (idol f N)) X (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) t
 flavors :∀ W:Flavor N → ℂ,Matrix.diagonal W∈unitary _ → ∀ U, Parade U U (trade (flute (Lat.Row f) (Matrix.diagonal W))) X (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) t
lemma flowering (e₁:E→Dye)(e₂:J→Dye) (hp:PantryX f N R.threshold e₁ e₂ Y')(hv: Sacred G)(hz:Torch Γ)(hh:Run.Pack id id t p n (wood J' 0 O.land) q Γ D'): Loom.Fleet.Tolerant (rungC O d G Y' (τ:=τ) e₁ e₂) (X'):=by
   let F:= G.equip N B; let Y:= roof F Y' 30 B; let A:=deckHue H F Y' Y; let T':= VarnC H U N; let Z:=sailP H Γ N
   have hs: S=sliceL O d:=rfl
   let l (z:Lat.Frame c):= constantGauge z S; have h z:(l z) ∘ (S).embed=z:= funext fun i=>congr_arg z ((S).embed_parent i)
   let z:= fun _:Site c => (1:su.El); have hl x: Lattice.gauge (l z) x=x:=presenceP _
   refine ⟨?_,?real, ?_,?_⟩
   case real=>
      refine graft A ?_ (graft T' (A:=Z) (boon H U _ z ?_) (horn H hz)) 
      · have hV i: Usher S F (Lattice.gauge (l z) i) i (dawn (whole (idol f N) (idol c N))) (dawn (idol f N)) (dawn (idol c N)) (Equiv.refl _) (Equiv.refl _):=by rw [hl]; exact amber G N B _ hv
        exact gaugeP H F Y' z hV (fun U=> by rw [show Lattice.gauge _ U=U from hl U]; exact hp.real U)
      · intro i x; rw [show Lattice.gauge _ x=x from hl x]; exact Port.palm ..
   · rintro ⟨t,b'⟩ v g hb
     obtain ⟨t',ht,hx⟩:= sheetsX (S) (t,b') v g hb
     obtain ⟨e,k,heK,heL,hf⟩:= hp.turns _ t' v ht
     obtain ⟨π,hm⟩:= mac_m (δ:=δ) (b:=b) (R:=R) (β:=β) (T:=T) t b'
     let W:=trade (copies N (haze (t,b') v g))
     have hv' := (fun U:Grid f=> Sway.remoteG G N B U (t,b') t' v ht hv)
     let U₁:= copies N (TrU S (t,b') t' v); let V:= copies N (TrV S (t,b') t' v)
     have he: W=trade V:=by unfold W; rw [hx]; rfl
     have hf' X: Parade (pull t ((S).embed b') X) X (trade U₁) Y' (StepData.sendSites t ((S).embed b')) e k R.threshold:=by
        convert! hf X -- Equiv.Perm defeq? inspect
     have hp X: Usher S F (pull t ((S).embed b') X) X (trade (whole U₁ V)) (trade U₁) W (StepData.sendSites t ((S).embed b')) (Equiv.sumCongr (raiseS S (t,b')) (raiseS S (t,b'))):=by
        rw [he]; convert! hv' X
     obtain ⟨uP,huP,huΩ⟩:= purposed H F Y' e₁ e₂ hp hf' heK heL π hm
     refine ⟨π,_,jointly A huP (jointly T' (cycles H U hs t b' g v ht hx π) (cache H hz t b' g v hb π)), fun i=> ?_⟩ -- he shadow
     rcases i with i|i; exact huΩ i; exact rfl
   · intro z'; let P:=trade (rotates N (l z')); let T':=trade (rotates N z') -- shadow
     have hf: trade (rotates N z')= trade (rotates N ((l z') ∘ (S).embed)):=by rw [h]
     have he X: Usher S F (Lattice.gauge (l z') X) X (trade (whole (rotates N (l z')) (rotates N ((l z') ∘ (S).embed)))) P (trade (rotates N z')) (Equiv.refl _) (Equiv.refl _):=by rw [hf]; exact Sway.heatE G N B X _
     refine graft A (gaugeP H F Y' z' he (fun U=> Loom.outfit H Y' hp.frame U _)) (graft _ (boon H U _ z' ?_) (Villa.mesh H hh z'))
     rw [hf]; exact fun i U'=> triumph U N B i _ _
   intro W1 hW; let W:= Matrix.diagonal W1
   let Ψ:=flute (Lat.Row f) W; let Ψ':=flute (Lat.Row c) W
   have hF X: Usher S F (Lattice.gauge (l z) X) X (trade (whole Ψ Ψ')) (trade Ψ) (trade Ψ') (Equiv.refl _) (Equiv.refl _):=by rw [hl]; exact Sway.fluteE G N B X _ hW
   have hpX X: Parade (Lattice.gauge (l z) X) X (trade Ψ) Y' (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) R.threshold:=by rw [hl]; exact hp.flavors _ hW _
   exact graft A (gaugeP H F Y' z hF hpX) (graft T' (boon H U (trade Ψ') z (fun i x=>by rw [show Lattice.gauge _ x=x from hl x]; exact Port.fluteRy U W hW x i)) (ribbon H W hW))
variable (e:E→Dye)(j₁:J→Dye)
def evalRise (V:E→Grid f→EvenA f N) (Z:J→Grid f→EvenA f N):Rise f N E J:=⟨Y'.row,Y'.front,V,Z⟩
variable (x s:ℂ) (V:E→Grid f→EvenA f N)(Z:J→Grid f→EvenA f N)
omit [Countable E] [Countable J] [Fintype D] in
lemma tintP (w:Finset (Fj D E J)):pigment (taxes e j₁ w) x s=Weight (fun i=>pigment (e i) x s) (fun j=>pigment (j₁ j) x s) w:=by
   unfold taxes Weight; rw [← pigment_sum,← pigment_sum]; exact map_mul (Struck.lane x s) (Multiplicative.ofAdd _) (Multiplicative.ofAdd _)
variable (hV: ∀ i U, NormedSpace.exp ((evalRise Y' V Z).reading R.threshold U i)-1=pigment (e i) x s •(NormedSpace.exp (Y'.reading R.threshold U i)-1)) (hZ:∀ j W,Z j W=pigment (j₁ j) x s • Y'.plug j W)
include hV hZ
local notation "Y!"=> (evalRise Y' V Z)
local notation "Z'"=> tableau O d K Y! H G U Γ
local notation "M!"=> (rungC O d G Y' (τ:=τ) e j₁)
omit [Countable E] [Countable J] in
lemma age (Γ:Land c (Site c) (Site c)) : let W:= tableau O d K Y' H G U Γ; tableau O d K (evalRise Y' V Z) H G U Γ=tableauM W (rungC O d G Y' (τ:=τ) e j₁) x s:=by
    intro W; let W':=tableau O d K Y! H G U Γ
    let T:=tableauM W M! x s
    have he: W'.works=T.works:=by
       funext i A X₁; rcases i with i|i
       · have hh:=inkDegree (H₁:=H) (G.equip N B) Y' V Z (fun i=>pigment (e i) x s) (fun j=>pigment (j₁ j) x s) hV hZ i A X₁ -- shadow V / h.ratio args
         rw [← tintP] at hh; exact hh
       change W.works (.inr i) A X₁=pigment (0,0) x s • W.works (.inr i) A X₁; simp [Struck.pigment]
    change W'=T; exact congr_arg (version W) he -- rfl?
omit hV hZ
end YM.QCD.Villa

#print axioms YM.QCD.Villa.flowering
#print axioms YM.QCD.Villa.age
