import YM.QCD.Pant.Success
import YM.MassiveQCD.Palette.Symmetry
/-! # Spin & gauge alignment at every REAL marker, before purchasing P≥1.

 Keep Γ strict so can use the same cabins relief at the zero-marker as the unmarked.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Patron
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets Horticulture
open Mixed Reserves Trees Beam Cove Leaf Lat PhysicalNext.Repeat.Greenbelt Loom Fleet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{δ β τ μ W C:ℝ} {R:Rep su f}{F Z:Tree.Forest S.ratio}{Q:Target su P}{o :Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι:Type}{N:ℕ}
local notation "I"=> Pipe.Clump S ι
local notation "C'"=>Coat T
variable (Y:Fleet H ι N)
set_option quotPrecheck false
open Art Blaze Polar Shield Frond
open Grass Cove Lat GasP Filter Ursell Graph
open Sway OrbitG Villa Loom Bay Strut
variable {K: EvenA c N→+*EvenA c N}
-- Pan not on Gospel. duplicate to arbitrary Y.
structure Colorful :Prop where
 travel (s:Strut c)(p :Spike)(g: Site c→ℂ): Warrant s g p→∃ (π:R.activities.Moves s.1 (S.ratio.embed s.2))(Ω:Equiv.Perm ι), Y.Marches π Ω (trade (copies N (Strut.haze s p g))).passL
 warp z: Y.sings z (trade (Lat.rotates N z)).passL
 real : Y.sings (fun _=>1) (dawn (idol c N)).passL
 genre (W:Matrix (Flavor N) (Flavor N) ℂ): Patron.Chord W → Y.sings (fun _=>1) (trade (flute (Lat.Row c) W)).passL

end YM.QCD.Patron
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
structure Portrait (n:Side)(F:ℕ) (t:ℝ) {E J :Type} (Z:Rise n F E J) :Prop where
 refr : Z.Reframe
 turns (v:Strut n)(g:Site n→ℂ)(V:Spike): Warrant v g V → ∃ e j,∀ U,Parade (Strut.sky v U) U (trade (Lat.copies F (Strut.haze v V g))) Z (Strut.act v) e j t
 real : ∀ U, Parade U U (dawn (idol n F)) Z (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) t
 flavors :∀ W:Matrix (Flavor F) (Flavor F) ℂ,Patron.Chord W → ∀ U, Parade U U (trade (flute (Lat.Row n) W)) Z (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) t
variable {W' :ℕ→Atom su 2}{J':Plan k}
variable (O:Flight j k)(K: KernelChoices)(d:f.val=c.val*O.L.val)
set_option quotPrecheck false
local notation "S"=> (O.visit K d).ratio
variable {T : Tube su (O.visit K d)}
variable {X:Grid f→Sheet f} (H:Cash W τ μ O.L Q o C T (trimP T R δ β b))(G:Sun O c f d η h z a a' m X) (U :Swathe O d X W' J' h η a u v i)
variable {Γ: Land c (Site c) (Site c)}{D':Pays c (Site c) (Site c)}

set_option quotPrecheck false
local notation "Z'"=> trimP T R δ β b
variable (Y': Rise f N E J)
local notation "X'"=> tableau O d K Y' H G U Γ
set_option maxHeartbeats 550000 in
lemma irisInk (hp:Portrait f N R.threshold Y')(hv: Sacred G)(_hW:Y'.Wave R.threshold)(hz:Torch Γ)(hh:Run.Pack id id t p n (wood J' 0 O.land) q Γ D'): Patron.Colorful (X'):=by
   let F:= G.equip N B; let Y:= roof F Y' 30 B; let A:=deckHue H F Y' Y; let T':= VarnC H U N; let Z:=sailP H Γ N
   have hs: S=sliceL O d:=rfl
   let l (z:Lat.Frame c):= constantGauge z S; have h z:(l z) ∘ (S).embed=z:= funext fun i=>congr_arg z ((S).embed_parent i)
   let z:= fun _:Site c => (1:su.El); have hl x: Lattice.gauge (l z) x=x:=presenceP _
   refine ⟨?_,?_,graft A ?_ (graft T' (A:=Z) (boon H U _ z ?_) (horn H hz)),?_⟩ -- A implicit etc
   · rintro ⟨t,b'⟩ v g hb
     obtain ⟨t',ht,hx⟩:= sheetsX (S) (t,b') v g hb
     obtain ⟨e,k,hf⟩:= hp.turns _ t' v ht
     obtain ⟨π,hm⟩:= mac_m (δ:=δ) (b:=b) (R:=R) (β:=β) (T:=T) t b'
     let W:=trade (copies N (haze (t,b') v g))
     have hv' := (fun U:Grid f=> Sway.remoteG G N B U (t,b') t' v ht hv)
     let U₁:= copies N (TrU S (t,b') t' v); let V:= copies N (TrV S (t,b') t' v)
     have he: W=trade V:=by unfold W; rw [hx]; rfl
     have hf' X: Parade (pull t ((S).embed b') X) X (trade U₁) Y' (StepData.sendSites t ((S).embed b')) e k R.threshold:=by
        convert! hf X -- Equiv.Perm defeq? inspect
     have hp X: Usher S F (pull t ((S).embed b') X) X (trade (whole U₁ V)) (trade U₁) W (StepData.sendSites t ((S).embed b')) (Equiv.sumCongr (raiseS S (t,b')) (raiseS S (t,b'))):=by
        rw [he]; convert! hv' X
     obtain ⟨uP,huP⟩:= pureP H F Y' hp hf' π hm
     exact ⟨π,_,jointly A huP (jointly T' (cycles H U hs t b' g v ht hx π) (cache H hz t b' g v hb π))⟩ -- he shadow
   · intro z'; let P:=trade (rotates N (l z')); let T':=trade (rotates N z') -- shadow
     have hf: trade (rotates N z')= trade (rotates N ((l z') ∘ (S).embed)):=by rw [h]
     have he X: Usher S F (Lattice.gauge (l z') X) X (trade (whole (rotates N (l z')) (rotates N ((l z') ∘ (S).embed)))) P (trade (rotates N z')) (Equiv.refl _) (Equiv.refl _):=by rw [hf]; exact Sway.heatE G N B X _
     refine graft A (gaugeP H F Y' z' he (fun U=> Loom.outfit H Y' hp.refr U _)) (graft _ (boon H U _ z' ?_) (Villa.mesh H hh z'))
     rw [hf]; exact fun i U'=> triumph U N B i _ _
   · have hV i: Usher S F (Lattice.gauge (l z) i) i (dawn (whole (idol f N) (idol c N))) (dawn (idol f N)) (dawn (idol c N)) (Equiv.refl _) (Equiv.refl _):=by rw [hl]; exact amber G N B _ hv
     exact gaugeP H F Y' z hV (fun U=> by rw [show Lattice.gauge _ U=U from hl U]; exact hp.real U)
   · intro i x; rw [show Lattice.gauge _ x=x from hl x]; exact Port.palm ..
   intro W hW
   let Ψ:=flute (Lat.Row f) W; let Ψ':=flute (Lat.Row c) W
   have hF X: Usher S F (Lattice.gauge (l z) X) X (trade (whole Ψ Ψ')) (trade Ψ) (trade Ψ') (Equiv.refl _) (Equiv.refl _):=by rw [hl]; exact Sway.fluteE G N B X _ hW.1
   have hpX X: Parade (Lattice.gauge (l z) X) X (trade Ψ) Y' (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) R.threshold:=by rw [hl]; exact hp.flavors _ hW _
   exact graft A (gaugeP H F Y' z hF hpX) (graft T' (boon H U (trade Ψ') z (fun i x=>by rw [show Lattice.gauge _ x=x from hl x]; exact Port.fluteRy U W hW.1 x i)) (ribbon H W hW.1))
open Patron
variable {ι α:Type}[Countable ι][Countable α] (V : Gem c N ι) (F : Patron.Rail c N α)
lemma painted_ink (h: Patron.Keyed V)(hp:Patron.MixedInk F) (t:ℝ): Villa.Portrait c N t (duo V F):=by
    refine ⟨⟨h.notes.gauge,hp.gauge⟩,?_,fun U=> Villa.permanence _ _ _ (fun i U=> h.notes.real i U) (fun i U=>hp.real i U) U,fun W hv U=> Villa.permanence _ _ _ (fun i U=> h.notes.num i U W hv) (fun i U=> hp.num i U W hv) U⟩
    intro v g k hh; obtain ⟨e,he⟩:=h.turns v k g hh; obtain ⟨d,hQ⟩:=hp.moves v g k hh; refine ⟨e,d,fun U=>⟨Work.H03.flags_send .., ?_,?_,fun i=>(hQ i).1,fun i=>(hQ i).2.1,fun i=>(he i).2 U,fun i=>(hQ i).2.2 U⟩⟩
    · exact fun i=> congr_arg RegularAddress.support (he i).1
    exact fun i=> congr_arg RegularAddress.site (he i).1
end YM.QCD.Villa
