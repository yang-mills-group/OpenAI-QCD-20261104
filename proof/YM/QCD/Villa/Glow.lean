import YM.QCD.Villa.Zinc
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
open AnalyticBridge.GaussianFieldAlignment Locations Channels PhysicalNext.Repeat.Turn Next.Fluctuations Next.SectorChange
local notation "B" => radiusB τ
open Sway OrbitG Strut Revolve
structure Pant (n:Side)(F:ℕ) (t:ℝ) {E J :Type} (Z:Rise n F E J) :Prop where
 refr : Z.Reframe
 turns (v:Strut n)(g:Site n→ℂ)(V:Spike): Warrant v g V → ∃ e j,∀ U,Parade (Strut.sky v U) U (trade (Lat.copies F (Strut.haze v V g))) Z (Strut.act v) e j t
 real : ∀ U, Parade U U (dawn (idol n F)) Z (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) t
 flavors :∀ W:Matrix (Flavor F) (Flavor F) ℂ,W∈unitary _ → ∀ U, Parade U U (trade (flute (Lat.Row n) W)) Z (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) t
variable {W' :ℕ→Atom su 2}{J':Plan k}
variable (O:Flight j k)(K: KernelChoices)(d:f.val=c.val*O.L.val)
set_option quotPrecheck false
local notation "S"=> (O.visit K d).ratio
variable {T : Tube su (O.visit K d)}
variable {X:Grid f→Sheet f} (H:Cash W τ μ O.L Q o C T (trimP T R δ β b))(G:Sun O c f d η h z a a' m X) (U :Swathe O d X W' J' h η a u v i)
variable {Γ: Land c (Site c) (Site c)}{D':Pays c (Site c) (Site c)}
lemma sheetsX (Vv:Ratio c f)(p:Strut c)(q:Spike)(g:Site c→ℂ)(hp:Warrant p g q): ∃ w:Site f→ℂ,Warrant (raise Vv p) w q∧ g=w ∘ Vv.embed :=by
   let z:= raise Vv p; obtain ⟨t,P,h⟩:=secure z
   have hv: Warrant z t q:=⟨h.1,hp.2⟩
   obtain ⟨u,v,hu,hx,hv',hH,hW⟩:= unique_scalar hp (mist Vv p hv)
   rcases mul_self_eq_one_iff.mp hu with rfl|hf
   · exact ⟨t,hv,funext (fun i=> by rw [hW,one_mul])⟩
   refine ⟨fun i=> -t i,⟨⟨?_,?_⟩,hp.2⟩,funext fun i=> ?_⟩
   · intro i; rcases hv.1.sign i with hk|hk <;> simp [hk]
   · intro i x; rw [mul_neg,neg_mul]; exact congr_arg Neg.neg (h.1.reflects i x)
   rw [hW,hf]; simp
set_option quotPrecheck false
local notation "Z'"=> trimP T R δ β b
variable (Y': Rise f N E J)
structure Pan {ι:Type} (X:Fleet H ι N):Prop where
 travel (v:Strut c)(g:Site c→ℂ)(V: Spike) : Warrant v g V→∃ (π:(trimP T R δ β b).activities.Moves v.1 ((S).embed v.2)) (w: Equiv.Perm ι), X.Marches π w (trade (Lat.copies N (Strut.haze v V g))).passL
 warp z: X.sings z (trade (Lat.rotates N z)).passL
 basis : X.sings (fun _=>1) (dawn (idol c N)).passL
 genre (W:Matrix (Flavor N) (Flavor N) ℂ): W∈unitary _ → X.sings (fun _=>1) (trade (flute (Lat.Row c) W)).passL
 speaks : X.speaking
local notation "X'"=> tableau O d K Y' H G U Γ
lemma irisA (hp:Pant f N R.threshold Y')(hv: Sacred G)(hW:Y'.Wave R.threshold)(hz:Torch Γ)(hh:Run.Pack id id t p n (wood J' 0 O.land) q Γ D')(hr:0<t)(hG:0<η): Pan O K d H (X'):=by
   let F:= G.equip N B; let Y:= roof F Y' 30 B; let A:=deckHue H F Y' Y; let T':= VarnC H U N; let Z:=sailP H Γ N
   have hs: S=sliceL O d:=rfl
   let l (z:Lat.Frame c):= constantGauge z S; have h z:(l z) ∘ (S).embed=z:= funext fun i=>congr_arg z ((S).embed_parent i)
   let z:= fun _:Site c => (1:su.El); have hl x: Lattice.gauge (l z) x=x:=presenceP _
   refine ⟨?_,?_,graft A ?_ (graft T' (A:=Z) (boon H U _ z ?_) (horn H hz)),?_,voice A (hue_voice H F Y' hW) (voice T' (varnV H U hG) (Villa.visible H hh hr))⟩ -- A implicit etc
   · rintro ⟨t,b'⟩ g v hb
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
   have hF X: Usher S F (Lattice.gauge (l z) X) X (trade (whole Ψ Ψ')) (trade Ψ) (trade Ψ') (Equiv.refl _) (Equiv.refl _):=by rw [hl]; exact Sway.fluteE G N B X _ hW
   have hpX X: Parade (Lattice.gauge (l z) X) X (trade Ψ) Y' (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) R.threshold:=by rw [hl]; exact hp.flavors _ hW _
   exact graft A (gaugeP H F Y' z hF hpX) (graft T' (boon H U (trade Ψ') z (fun i x=>by rw [show Lattice.gauge _ x=x from hl x]; exact Port.fluteRy U W hW x i)) (ribbon H W hW))
end YM.QCD.Villa
