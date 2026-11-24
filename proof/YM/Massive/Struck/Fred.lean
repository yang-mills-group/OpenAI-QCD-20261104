import YM.Massive.Struck.Dye
import YM.Massive.Filament.Eruption
import YM.Massive.Filament.Foil
/-! # Symmetry carried on tagged stencils. The Arc input evaluates at λ complex and
its colors don't inherit Regal. Reversibility needed only on the real observer axis. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Loom.Fleet
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets Horticulture
open Mixed Reserves Trees Beam Cove Leaf Lat PhysicalNext.Repeat.Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{δ β τ μ W C:ℝ} {R:Rep su f}{F Z:Tree.Forest S.ratio}{Q:Target su P}{o :Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι:Type}{N:ℕ}
local notation "I'"=> Pipe.Clump S ι
variable (Y:Fleet H ι N)
open Art Blaze Polar Shield Frond GasP Ursell Graph Patron Bay Strut
open AnalyticBridge.GaussianFieldAlignment Locations Channels PhysicalNext.Repeat.Turn Next.Fluctuations Next.SectorChange
open Struck Massive.Filament Sway Pith OrbitG Fibre
variable (B:ι→Dye)
variable {p:Strut c}{π:R.activities.Moves p.1 (S.ratio.embed p.2)}{Ω:Equiv.Perm ι}{k:Spike}{g: Site c→ℂ}
variable (h:Y.Marches (s:=p.1) (b:=p.2) π Ω (Diode N p k g))(he:∀ i,B (Ω i)=B i)
local notation "X!"=> fun i=>pigment (B i)
variable {χ:Chi}
def toner (z:Clusters Y.Bright): Dye:= ∑ i, ∑ j∈(z.2 i).val.toRight,B j -- unmarked if power0. use at HP
abbrev tableauM (z s:ℂ) := version Y (fun i U V=> pigment (B i) z s • Y.works i U V) -- flex
lemma potency (z:Clusters Y.Bright) (h:∀ i,Ash (B i)) : Ash (toner Y B z):=bright_sum _ _ fun _ _ => bright_sum _ _ fun i _=> h i
lemma tonerE (z:Clusters Y.Bright)(x s:ℂ): pigment (toner Y B z) x s= Y.marked_amount (fun i=> pigment (B i) x s) z:= by unfold toner; simp_rw [pigment_sum]; rfl
lemma toner_earn (z:Clusters Y.Bright)(x s:ℂ)(V:Grid c): honest (tableauM Y B x s) χ V z=pigment (toner Y B z) x s • Y.honest χ V z:=by rw [tonerE]; exact honest_scaled Y _ _ (fun i U V=>rfl) ..
lemma toner_gem (z:Clusters Y.Bright)(X:Clusters Y.Bright→RegularAddress c)(x s:ℂ): (crude (tableauM Y B x s) χ X).view z=pigment (toner Y B z) x s • (crude Y χ X).view z:=by rw [tonerE]; exact crude_scaled Y _ _ (fun i U V=>rfl) ..
include he h
lemma toner_shift (x:Clusters Y.Bright): toner Y B (Patron.pack (adawn (p:=p) Y h) x)=toner Y B x:=by
   apply sum_congr rfl; intro i _; change ∑ j∈(toRight (rune π Ω (x.2 i).val)), B j=_; rw [legR,show Ω.finsetCongr _= ((x.2 i).val.toRight).image Ω from Finset.map_eq_image .., sum_image Ω.injective.injOn]; exact sum_congr rfl (fun i _=> he i)
lemma shadow (x s:ℂ): (tableauM Y B x s).Marches π Ω (Diode N p k g):=by
   refine ⟨h.cont,h.days,h.paths,h.glasses,h.groups,fun i U V=>?_⟩
   change pigment (B (Ω i)) x s • Y.works (Ω i) U V= sways _ (pigment (B i) x s • Y.works i _ _)
   rw [he,h.turns,complexFactor]
lemma flight (hf:Y.Famous)(s t:ℂ)(V:Grid c)(z:Clusters Y.Bright): let M:=tableauM Y B s t; Diode N p k g (M.honest χ (sky p V) z)= M.honest χ V (Patron.pack (adawn (p:=p) Y h) z):=by
    intro M; rw [show M.honest .. = _ from (toner_earn Y B (χ:=χ) z s t (sky p V)), complexFactor,gistE Y h hf]
    change pigment _ _ _ • _=honest (tableauM Y B s t) _ _ _; rw [toner_earn, toner_shift Y B h he]
omit he h
-- No slots slicing.H colors we need only λ-family equality of shift (using wear & marks) outside MarkLead.Total. but symmetry as HR.
structure Tolerant (X:Fleet H ι N):Prop where
 travel (s:Strut c)(p :Spike)(g: Site c→ℂ): Warrant s g p→∃ (π:R.activities.Moves s.1 (S.ratio.embed s.2))(Ω:Equiv.Perm ι), X.Marches π Ω (Diode N s p g) ∧ ∀ i,B (Ω i)=B i
 real : X.sings (fun _=>1) (Regal c N)
 warp z: X.sings z (sways (Lat.rotates N z))
 genre (W: Flavor N → ℂ): Matrix.diagonal W∈unitary _ → X.sings (fun _=>1) (sways (flute (Lat.Row c) (Matrix.diagonal W)))
-- independent of κ sign.
lemma tonic (hp:Tolerant B Y)(x s:ℝ): Tolerant B (tableauM Y B x s):=by
   let M:=tableauM Y B x s
   have he (K:EvenA c N→+*EvenA c N) (z:Site c→su.El)(h:Y.sings z K): M.sings z K:=by
      refine ⟨h.cont,fun i U V=>?_⟩; unfold M tableauM version; dsimp only; rw [← qr]; exact (eSM _ h.cont (s^(B i).2*x^(B i).1) _).trans (congr_arg _ (h.verse i U V))
   refine ⟨?_,he _ _ hp.real, fun z=>he _ _ (hp.warp z), fun w hw=> he _ _ (hp.genre w hw)⟩
   intro p k g h; obtain ⟨π,Ω,hπ,hΩ⟩:= hp.travel p k g h; exact ⟨π,Ω,shadow Y B hπ hΩ ..,hΩ⟩
-- Grit on crude
lemma Tolerant.course (hp:Tolerant B Y) (q:Clusters Y.Bright) (A:Clusters Y.Bright → RegularAddress c): Grit ((crude Y χ A).view q):=by
    refine ⟨shaded _,fun V=>?_, estate _ (fun U=> furnaceW Y hp.real (imp _ (gammaL ..)) ..)⟩
    let f(U:Grid c):= Y.furnace χ U q; intro w hw; change sways _ (pepper f V)=_
    unfold pepper; rw [eVoc _ (phare _) (surfeit (unit_f hw))]; apply integral_congr_ae; filter_upwards with z; exact (choirT (siteRot z) (Matrix.diagonal w) _).symm.trans (congr_arg (sways _) (furnaceW Y (hp.genre w hw) (surfeit (unit_f hw)) _ (gauge z V) q))
    -- warning metavariables
lemma Tolerant.fleeting (hp:Tolerant B Y)(hf:Y.Famous)(χ:Chi)(hh:∀ V,Summable (fun i=> Y.honest χ V i)) (x): Grit (fun V=> Y.mission χ V x):=by
    refine ⟨fun V k=>congr_arg Subtype.val (marchW Y (hp.warp k) hf χ V (hh _) _),fun U J hJ=>?_,fun U=>?_⟩
    · have hx:= marchW Y (hp.genre J hJ) hf χ U (hh _) x; rw [Villa.presenceP] at hx; exact hx
    have hx:= marchW Y hp.real hf χ U (hh _) x; rw [Villa.presenceP] at hx; exact hx
include h he
-- Because of carriable Ω march the transformed old eb-π on *master Y* transports all frame-copies on ANY ν. No conjugacy for complex axis. Weight-preserving geometry is enough. Use flexClaim explicit.
lemma swingerF (χ:Chi)(x s:ℂ)(hp:(tableauM Y B x s).Famous)(hS:∀ V,Summable (fun i=> (tableauM Y B x s).honest χ V i)) (V:Grid c)(i:Y.Faber): let Q:= flexClaim Y χ (tableauM Y B x s).works; Diode N p k g (Q.warp i (sky p V))= Q.warp ((ebonyJ (p:=p) Y h) i) V:=by
    let Q:= tableauM Y B x s; have hQ : Q.Marches π Ω (Diode N p k g):=shadow Y B h he ..
    intro V₀
    
    exact waistF Q hQ hp χ V (hS _) i.val -- but RHS projection e map defeq -- test
omit h he
abbrev journal (χ:Chi)(x s:ℂ): Rail c N Y.Faber:= flexClaim Y χ (tableauM Y B x s).works
lemma memoir (χ:Chi)(hp:Tolerant B Y)(s:ℝ) (hf:∀ z:ℝ, ‖z‖<1→ (tableauM Y B z s).Famous)(hS:∀ z:ℝ, ‖z‖<1→ ∀ V,Summable (fun i=> (tableauM Y B z s).honest χ V i)): MatchX (fun x=> journal Y B χ x s):=by
    refine ⟨fun z i hz=> (?_ : Grit (fun V=> (tableauM Y B z s).mission χ V i.val)),?_⟩
    · exact Tolerant.fleeting _ _ (tonic Y B hp z s) (hf z hz) χ (hS z hz) _
    intro p k g hP; obtain ⟨π,e,hπ,hΩ⟩:=hp.travel p k g hP; refine ⟨ebonyJ (p:=p) Y hπ,fun x hx i=>?_⟩
    let f:= claim Y χ; let u:= ebonyJ (p:=p) Y hπ
    refine ⟨(show (f.addr (u i)).place=(f.addr i).place.image (act p) from ?_), (show (f.addr (u i)).inv=(f.addr i).inv.image (act p) from ?_),fun V=>swingerF Y B hπ hΩ χ (x:ℂ) s (hf x hx) (fun V=>hS x hx V) V i⟩
    · exact womb (postP (mermaid (p:=p) Y hπ)) _
    exact shaftsG (seedD (p:=p) Y hπ) _
-- thermostat Arc assembler λ disks, also useful for hypothesis orientation at chosen real master.
lemma Tolerant.expand (χ:Chi) (hQ:Tolerant B Y)(hA:∀ i,Ash (B i))(hf:∀ (z s:ℂ), ‖z‖<1→‖s‖<1→ (tableauM Y B z s).Famous)(hT:∀ V:Grid c,Summable (fun i=> Y.honest χ V i)): Arc (fun z s=> journal Y B χ z s) ∧ ∀ s:ℝ, ‖s‖<1→ MatchX (fun z=> journal Y B χ z s):=by
    let p (z s:ℂ):= (tableauM Y B z s).works
    let H' i:=pigment (B i); have ht i: Fused (H' i):= prime _ (hA i); have hx i (z s:ℂ)(hz:‖z‖<1)(hs:‖s‖<1): ‖H' i z s‖≤1:= upperPaint _ z s hz.le hs.le
    refine ⟨arc_claim Y p χ H' ht hx (fun i U V z s _ _=>rfl) hT hf,fun s hs=>?_⟩
    apply memoir Y B χ hQ s (fun z hz=> hf z s ((Complex.norm_real _).trans_lt hz) ((Complex.norm_real _).trans_lt hs))
    intro z hz V; exact ((hT V).norm.of_nonneg_of_le (fun _=>norm_nonneg _) (fun y=> fdr Y p χ H' hx (fun i U V z s hz hs=>rfl) V y z s ((Complex.norm_real _).trans_lt hz) ((Complex.norm_real _).trans_lt hs))).of_norm
-- hold total E orientation on master. For any η version AND any filter by degree, spins honor.K.Power. uniform cost
lemma opaquePS (A:Clusters Y.Bright→RegularAddress c)(χ:Chi)(H:∀ k, Y.sings k (sways (Lat.rotates N k)))(hF:Y.Famous)(hA:∀ i,(A i).support=GasP.seatP Y.lightF i) (V:Grid c)(i:Clusters Y.Bright): letters (crude Y χ A) (Pressure.temp τ) V i= Y.honest χ V i :=by
   let t:= Pressure.temp τ;let T i V:= Y.furnace χ V i; change masked t (A i).support _ V=_; rw [hA i]; apply congr_fun (peppy (T i) t (GasP.seatP Y.lightF i) ?_) V
   intro U k; suffices h: sways (Lat.rotates N k) (Y.honest χ (gauge k U) i)=Y.honest χ U i by exact congr_arg Subtype.val h
   rw [phoenix Y χ _ hF,phoenix Y χ _ hF]; let K:=trade (Lat.rotates N k); unfold termP; change K.passL _ = _; rw [eSM K.passL K.phare,eSM K.passL K.phare,map_prod]; apply congr_arg; apply congr_arg; exact prod_congr rfl (fun j _=>Fleet.factor Y (H k) _ hF ..)
end YM.QCD.Loom.Fleet
#print axioms YM.QCD.Loom.Fleet.tonic
#print axioms YM.QCD.Loom.Fleet.Tolerant.expand
