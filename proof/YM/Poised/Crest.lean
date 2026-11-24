import YM.Poised.Prince
import YM.Poised.Furls
/-!
# Local ray/pressure nozzle with same Hart. Bills scaled before paired path. Input roots estimated back exactly.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG MassiveQCD.Plate MassiveQCD.Apron MassiveQCD.Elevator
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{β τ C μ W:ℝ}
variable {R Rx:Rep su f}{O O₁:BudgetPoint}{F:Tree.Forest S.ratio}{Q:Target su P}{o:Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι κ I E J D:Type}{N:ℕ}
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus PhysicalNext.Repeat.Sage PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir PhysicalNext.Repeat.Brim
open AnalyticBridge.SectorAffine.Offset Planned.AtomRegular
open QCD.Dust QCD.Brick Pipes Spice MassiveQCD.Lyre Shells Sands MultiNext.SignedSource.Ease
variable (Y:Fleet H ι N)(Γ :Cash W τ μ L Q o C T (lore Rx)) {X:Support f} {B:BudgetPoint}{n p d k l:ℕ}
local notation "Y?"=> Lat.Fields c 6
local notation "Y'"=> Lat.Fields f 6
variable {N': Libretto su n}{D:Heir.Record}{v u t M r q' χ' w w' x x₀ x' ρ θ δ Y₂ α Zx C':ℝ}{χ:Chi}
variable (b:Cover)(hP:Plays N' D B Rx.p P T τ)(hB:B.B=radiusB τ)(Vb:Hera.Rights su n)(i:ℕ)
set_option quotPrecheck false
local notation "Xo"=> ((Sands.lore Rx).activities.reg i)
local notation "Xⁱ"=> (Brim.plate Γ i)
local notation "Xt"=> T
-- general freeze metric.R
variable (T₀:Grid f → VectorD (Site f) (Faces (Site c)))
variable (F:Grid f→Lat.Fields f 6)(Ψ: EvenA c N →L[ℝ] Lat.Fields c 6)(n₀:ι)(h:∀ A: Grid f,Healthy Rx.p.threshold ((Sands.lore Rx).activities.reg i).support A →∀ V: Grid c,Ψ (Y.works n₀ A V)=changeVars (T₀ A) (F A))
variable (hX:Measurable F) (way:ℝ) (U:Lat.Fields c 6 →L[ℝ] ℝ) 
variable (V:Support f)(hV:V⊆((lore Rx).activities.reg i).support)(w₀:ℝ)
variable (hu:0<u)(ht:0<t)(he:Charm Rx.p V F)(hq:Rooted V F)
variable (hM: t*(2^p:ℝ)*w₀ ≤ C'*u)(hC':1 ≤ C') (hh:0 ≤ w₀)
variable (hvP:∀ U', Healthy Rx.p.threshold ((lore Rx).activities.reg i).support U'→ Stanch V S.ratio (T₀ U') p w₀)
local notation "Fo"=> ((lore Rx).activities.reg i).site
local notation "Go"=> (Brim.plate Γ i).site
variable (hlp:Rx.p.supBounds ((lore Rx).activities.reg i).site V (framesF (purseX ((lore Rx).activities.reg i).site p u) ∘ (mantel k ∘ F)) x)
variable (α':ℝ)(p':ℕ)(hq₀:P.Funds S T)(o'' e g' gn: ℕ) (hg':Rx.p.power=p')(X₂ X₃ A₀:ℝ) (hE:Fountain.ScrollX N' α' X₂ g' p' P)
variable (hA:∀ i j:Pipes.Shell,∀ x:su.Color,‖x‖≤1→Through n (yaw i j) x A₀)
variable (Z:VectorD (Site f) (Faces (Site c))) (hZ: Pipes.Heritage Rx.p ((lore Rx).activities.reg i).support b (purseX ((lore Rx).activities.reg i).site p u) (purseX (Brim.plate Γ i).site p t) g' (0,Z) (Kit.slope S.patch.L) X₃) (hQ:1 ≤ X₃)
variable (hν: Heir.clinicFee n D.Q*(Heir.loom B (Heir.reach τ) N'.C)^2 + D.ε*Rx.p.threshold ≤ (Kit.slope S.patch.L)^max g' 2 * Rx.p.threshold) (hb: (1+patterns n)*(A₀*(N'.M*Heir.loom B (Heir.reach τ) N'.C))*((Fintype.card Pipes.Shell:ℝ)*pup g' X₃ * (Kit.slope S.patch.L)^2) ≤ (Kit.slope S.patch.L)^max g' 2) (hm:N'.M*Heir.loom B (Heir.reach τ) N'.C ≤1)
variable (Θ:SourceRead.TaperHol)(hy:∀ (J:Labels.Jet su)(j:ℕ), j<g' → WardBin.leading j (Beacon.moment (d:=o'') Θ b J F)=0)(hI:wrap f b=((lore Rx).activities.reg i).site)(hS: Short S Rx.p ((lore Rx).activities.reg i).support)
variable (hK₀:o'' ≤ Rx.p.order)(hK₁:g' ≤ o''+1)(hK₂:g' ≤2*n)
variable (hY:∀ U:Grid f,∀ g:Frame c, Healthy Rx.p.threshold ((lore Rx).activities.reg i).support U → let W:=Lattice.gauge (g∘ S.ratio.parent) U; slots 6 g (changeVars (T₀ W) (F W))=changeVars (T₀ U) (F U))
variable (hG:∀ k U,slots 6 k (F (Lattice.gauge k U))=F U)
variable (hZ':pup g' X₃*(Kit.slope S.patch.L)^2 ≤ C')
variable {σ:ℝ}(ht':0 ≤ σ)(h₁:∀ (F0: Tree.Forest S.ratio)(k:S.Choices) (V' : Grid c) (g:Frame c),Healthy B.threshold (Brim.plate Γ i).support V' →Heir.Canvas B (Brim.plate Γ i).site (Heir.reach τ) V' g n N'.C → ∀ U:Grid f,Healthy Rx.p.threshold ((lore Rx).activities.reg i).support U → BeamRaw ((lore Rx).activities.reg i).support U (Sands.homeQ F0 Γ χ V' i k D) way → let A:=Lattice.gauge (g∘ S.ratio.parent) U; ∀ i':Faces (Site f),i'∈limits V→ (∑ j:Faces (Site c), purseX (Brim.plate Γ i).site p t j* ‖(T₀ A i' j-Z i' j)‖) ≤ σ*purseX (wrap f b) p u i')
local notation "w₁"=> purseX (Brim.plate Γ i).site p t
local notation "w₂"=> purseX (wrap f b) p u
include hlp b -- hp remove
include hX hP h hvP hM hh hC' he hq hu ht hS hI hy Θ hν hb hm hZ hZ' hE hQ hA hg' h₁ hY hG hK₀ hK₁ hK₂ Vb hq₀ hV ht'
set_option maxHeartbeats 480000 in
lemma payP (hU: ‖U‖ ≤1): Private Y B N' Γ χ D way n₀ i (plaque^k*(C'^k*x)) (plaque^k*((k:ℝ)*σ*C'^k*x)) (plaque^k*(Fountain.tithy k X₂ X₃ Vb g'*x*(Kit.slope S.patch.L)^g')) ((U.comp (framesF (purseX (Brim.plate Γ i).site p t))).comp ((mantel k).comp Ψ)):=by
    let W:= (Xo).support; let A:Grid f→Lat.Fields f 6:= mantel k ∘ F -- remove
    have ht₁:= purse_pos (Brim.plate Γ i).site p t ht; have ht₂:= purse_pos (wrap f b) p u hu
    have hp:A ∘ id=A:= rfl; have hφ:Charm Rx.p W A:=by
       have hz:Charm Rx.p W F:=⟨fun _ _ hr=> he.sites _ _ (fun j hx hy=> hr j (hV hx) (hV hy)),fun i hi=> he.smooth i (hi.mono_left hV)⟩; exact hz.scales _
    have hs:∀ U,A U ∈region (limits V):=fun _=> region_mantel _ _ _ (hq.2 _); have heA:∀ U,A U∈layer _ k:=fun _=>QCD.Stew.chamber _ _
    have hA' :Rx.p.supBounds (wrap f b) W (framesF w₂ ∘ A) x:=by rw [hI]; exact ⟨hlp.1,fun V hB l hl he'=>hlp.2 V (hB.mono_left hV) _ hl he'⟩
    have heℓ:=boxed1 S.patch.L
    have hHZ: Pipes.Heritage Rx.p W b w₂ w₁ g' (0,Z) (Kit.slope S.patch.L) X₃:=by unfold W; rw [hI]; exact hZ
    have hT' : SeatD w₂ w₁ Z C':= SeatD.less _ _ _ _ _ (Heritage.purse Rx.p W b (0,Z) w₂ w₁ heℓ.1 heℓ.2 hQ hHZ).2 hZ'
    have hZe i':∀ (_:i'∈limits V),(∑ j, w₁ j*‖Z i' j‖) ≤ C'*w₂ i':=fun _=> ((SeatD.from_weights _ _ _ _ ht₂ fun i=>(ht₁ i).le).1 hT').2 i'
    apply reachesP Y Γ b hP hq₀ p' p hg' Vb g' X₂ X₃ α' A₀ hA hE hν hb hm i hI hS Z A _ k Θ o'' T₀ n₀ _ _ hu ht ((mantel k).measurable.comp hX) hφ (fun U=>(regionMon (limitsMon _ _ hV)) (hs U)) heA (inherent F hG k) (inherits b F Θ ((he.smooth _ (AnalyticBridge.VerifiedReset.flat_ok ..)).of_le (by exact_mod_cast hK₀)) hy k hK₁) hHZ hQ hA' hK₀ hK₁ hK₂ way _ _ U hU -- order
    · intro V hV' W; change mantel _ (Ψ _)=_; rw [h V hV', Pika]; rfl
    · intro U' g hU' i'
      change slots 6 g (changeVars _ (mantel k _))=changeVars _ (mantel k _)
      rw [← Pika, ← Pika,← show ∀ X,mantel k (slots 6 g X)= slots 6 g (mantel k X) from Pika (signs g) k]; exact congr_arg (mantel k) (hY _ _ hU')
    · intro U' hU'
      refine (lane Z _ _ _ ht₂ ht₁ (zero_le_one.trans hC') hZe _ (hs _) (heA _)).trans (mul_le_mul_of_nonneg_left ?_ (pow_nonneg (zero_le_one.trans hC') _)); exact hA'.2 _ hU' [] (by simp) (by simp)
    intro F0 k' V' g hS hSg U' hU hx i'
    let W':=Lattice.gauge (g∘ S.ratio.parent) U'; have hW:Healthy Rx.p.threshold W W':=by unfold Healthy W'; rw [gauge_flags]; exact hU
    have hB i (hi:i∈limits V): (∑ j:Faces (Site c), w₁ j*‖T₀ W' i j‖) ≤ C'* w₂ i:=by rw [hI]; exact divisor t u ht hu Fo p (hvP W' hW) C' hh hM i hi
    have hp':= tenderV _ _ _ _ _ ht₂ ht₁ (zero_le_one.trans hC') σ ht' hC' hB hZe (h₁ F0 k' V' g hS hSg U' hU hx) (A W') (hs _) (heA _);
    exact hp'.trans (mul_le_mul_of_nonneg_left (show load _ (A W')≤ x from hA'.2 W' hW [] (by simp) (by simp)) (by positivity))
end YM.Massive.Poised
#print axioms YM.Massive.Poised.payP
