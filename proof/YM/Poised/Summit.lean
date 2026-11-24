import YM.Poised.Founts
import YM.QCD.Shell.Rome
/-!
# Economy gate on SMALL oracle.
λ calibrated caller provided for scalar roots. Shape estimates for all panelized moments eventually on same authenticated volumes. -/
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
open Sway OrbitG MassiveQCD.Plate MassiveQCD.Apron
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{β τ C μ W:ℝ}
variable {R Rx:Rep su f}{O O₁:BudgetPoint}{F:Tree.Forest S.ratio}{Q:Target su P}{o:Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι κ I E J D:Type}{N:ℕ}
variable (Y:Fleet H ι N)(Γ:Cash W τ μ L Q o C T (Sands.lore Rx))
variable {X:Support f} {B:BudgetPoint} {n p d k l :ℕ}  -- fix
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus PhysicalNext.Repeat.Sage PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir PhysicalNext.Repeat.Brim
open AnalyticBridge.LocalGaussian.Moments -- remove
open AnalyticBridge.SectorAffine.Offset Planned.AtomRegular
open QCD.Dust QCD.Brick Pipes Spice MassiveQCD.Lyre
variable {N': Libretto su n}{D:Heir.Record}{v u t M r q' χ' w w' x x₀ x' ρ θ δ Y₂ C':ℝ}{χ:Chi}
variable (b:Cover)(hP:Plays N' D B Rx.p P T τ)(hB:B.B=radiusB τ)(hPt:P.Funds S T)(p p₀:ℕ)(hR:Rx.p.power=p) (Vb:Hera.Rights su n)
local notation "R'"=> Rx.p
variable (k:ℕ)(I₀ I₂ α:ℝ)(ζ:ℝ)(hc:∀ i j:Pipes.Shell,∀ x:su.Color,‖x‖≤1→Through n (yaw i j) x ζ) (he:Fountain.ScrollX N' α I₀ k p P)
variable (hE: Heir.clinicFee n D.Q*(Heir.loom B (Heir.reach τ) N'.C)^2 + D.ε*Rx.p.threshold ≤ (Kit.slope S.patch.L)^max k 2 * Rx.p.threshold)
variable (hb: (1+patterns n)*(ζ*(N'.M*Heir.loom B (Heir.reach τ) N'.C))*((Fintype.card Pipes.Shell:ℝ)*pup k I₂ * (Kit.slope S.patch.L)^2) ≤ (Kit.slope S.patch.L)^max k 2) (hM:N'.M*Heir.loom B (Heir.reach τ) N'.C ≤1)
variable (i:ℕ)
set_option quotPrecheck false
local notation "Xo"=> ((Sands.lore Rx).activities.reg i)
local notation "Xⁱ"=> (Brim.plate Γ i)
variable (hQ:wrap f b=((Sands.lore Rx).activities.reg i).site) (hΓ:Short S Rx.p ((Sands.lore Rx).activities.reg i).support)
variable (Z:VectorD (Site f) (Faces (Site c)))(F:Grid f→Lat.Fields f 6)(Ψ: EvenA c N →L[ℝ] Lat.Fields c 6)(IΘ:ℕ)(Θ:SourceRead.TaperHol)(L':ℕ) -- output projection matrix context
variable (T₀:Grid f→VectorD (Site f) (Faces (Site c))) (n₀:ι)(h:∀ A: Grid f,Healthy Rx.p.threshold ((Sands.lore Rx).activities.reg i).support A →∀ V: Grid c,Ψ (Y.works n₀ A V)=changeVars (T₀ A) (F A)) (hA:∀ U:Grid f,∀ g:Frame c, Healthy Rx.p.threshold ((Sands.lore Rx).activities.reg i).support U → let W:=Lattice.gauge (g∘ S.ratio.parent) U; slots 6 g (changeVars (T₀ W) (F W))=changeVars (T₀ U) (F U))
variable (hu:0<u)(ht:0<t)(hX:Measurable F)(hp:MultiNext.SignedSource.Ease.Charm Rx.p ((Sands.lore Rx).activities.reg i).support F)
variable (hv: ∀ U,F U∈region (limits ((Sands.lore Rx).activities.reg i).support))(hζ:∀ U,F U∈layer _ IΘ) (hf:∀ k U,slots 6 k (F (Lattice.gauge k U))=F U) (hN:∀ (J:Labels.Jet su)(j:ℕ),j<k→WardBin.leading j (Beacon.moment (d:=L') Θ b J F)=0)
variable (hh: Pipes.Heritage Rx.p ((Sands.lore Rx).activities.reg i).support b (purseX (wrap f b) p₀ u) (purseX (Brim.plate Γ i).site p₀ t) k (0,Z) (Kit.slope S.patch.L) I₂) (hj:1 ≤ I₂) (hx: Rx.p.supBounds (wrap f b) ((Sands.lore Rx).activities.reg i).support (framesF (purseX (wrap f b) p₀ u) ∘ F) x)
variable (hm₁:L'≤ Rx.p.order)(hm₂:k ≤ L'+1)(hm₃:k ≤2*n)
variable (way:ℝ) (hZ:∀ U:Grid f, Healthy Rx.p.threshold ((Sands.lore Rx).activities.reg i).support U→ load (purseX (Brim.plate Γ i).site p₀ t) (changeVars Z (F U))≤ M)
variable (hy:∀ (F0: Tree.Forest S.ratio)(k:S.Choices) (V : Grid c) (g:Frame c),Healthy B.threshold (Brim.plate Γ i).support V →Canvas B (Brim.plate Γ i).site (Heir.reach τ) V g n N'.C → ∀ U:Grid f,Healthy Rx.p.threshold ((Sands.lore Rx).activities.reg i).support U → BeamRaw ((Sands.lore Rx).activities.reg i).support U (Sands.homeQ F0 Γ χ V i k D) way → let A:= Lattice.gauge (g∘ S.ratio.parent) U; load (purseX (Brim.plate Γ i).site p₀ t) (changeVars (T₀ A) (F A)-changeVars Z (F A))≤ v)
variable (U:Lat.Fields c 6 →L[ℝ] ℝ)(hU:‖U‖≤1)
include h hp hQ hP hΓ hA hZ hh hN hE hb hPt ht hu hx he hv hζ hM hc hR hX hf hy hU hj Θ Vb hm₁ hm₂ hm₃
set_option maxHeartbeats 620000 in
lemma reachesP :let K:=U.comp (framesF (purseX (Brim.plate Γ i).site p₀ t)); let C₁:=plaque^IΘ; Private Y B N' Γ χ D way n₀ i (C₁*M) (C₁*v) (C₁*(Fountain.tithy IΘ I₀ I₂ Vb k*x * (Kit.slope S.patch.L)^k)) (K.comp Ψ):=by
    intro K C₁; constructor; intro F' k' V' hp₁ hV YQ hspt hw
    let A:= (Brim.plate Γ i); let Xa:=(Sands.lore Rx).activities.reg i
    let q:= mapcase Γ i F'
    have hn:2≤ n:=by have h:=B.order_ge; have ht:=hP.rehearsed.test; omega
    let X:=Xa.support; have ho: wrap f b∈ X:= hQ.symm ▸ Xa.anchor; obtain ⟨g,hg⟩:= q.canvas Xa.site (Finset.mem_union_left _ Xa.anchor) hV hP.space N'.Z (by omega) hP.rehearsed.wire; have hg':Canvas B (S.ratio.parent (wrap f b)) (Heir.reach τ) V' g n N'.C:= hQ.symm ▸ hg -- rw orientation
    let Z':=leverL g IΘ; let L0:= U.comp Z'; let M0:= g ∘ S.ratio.parent; let J:=(L0.comp (framesF (purseX (Brim.plate Γ i).site p₀ t))).comp (Fountain.vat Z); let v0:= fun V:Grid f=>J (F (Lattice.gauge M0 V)); have ht: ‖L0‖≤ C₁:= (U.opNorm_comp_le Z').trans ((mul_le_of_le_one_left (norm_nonneg _) hU).trans (scepter ..))
    have heq:v0=(J.comp (mills M0⁻¹))∘F:= Fountain.oblique F hf _ J
    refine ⟨v0, heq.symm ▸ (fun X Y h'=>congr_arg (J.comp _) (hp.1 X Y h')),heq.symm ▸ (J.comp (mills M0⁻¹)).measurable.comp hX, ?_,?_,?_⟩
    · intro B' hx; refine (L0.le_opNorm (framesF (purseX (Brim.plate Γ i).site p₀ t) (changeVars Z (F (Lattice.gauge M0 B'))))).trans ?_; have hw:Healthy Rx.p.threshold Xa.support (Lattice.gauge M0 B'):=by unfold Healthy; rw [gauge_flags]; exact hx
      exact mul_le_mul ht (hZ _ hw) (norm_nonneg _) (zero_le_one.trans (one_le_pow₀ plaque_pos))
    · intro U' hx hV''; let B' := Lattice.gauge M0 U'; let H' := F B'; let Qv:=changeVars (T₀ B') H'; let Zu:= changeVars Z H'
      have he: K (changeVars (T₀ U') (F U'))=L0 (framesF (purseX (Brim.plate Γ i).site p₀ t) Qv):=by change U (framesF (purseX (Brim.plate Γ i).site p₀ t) (changeVars _ _))=U _; apply congr_arg U; rw [← hA U' g hx]; exact (remark g A.site _ Qv (exterior_layer _ (hζ B')) p₀).symm -- ht
      change ‖K (Ψ _)-L0 (framesF (purseX (Brim.plate Γ i).site p₀ t) Zu)‖ ≤ _; rw [h U' hx,he,← map_sub, ← map_sub]; apply (L0.le_opNorm _).trans; exact mul_le_mul ht (hy F' k' _ _ hV hg U' hx hV'') (norm_nonneg _) (zero_le_one.trans (one_le_pow₀ plaque_pos))
    unfold Sands.Horn
    have hG:0< gStep Rx.beta:= inv_pos.mpr (Real.sqrt_pos.mpr (show 0< Rx.beta from Γ.laws.intake.positive))
    -- call reached
    rw [←hQ]
    exact Fountain.reached (k:=k') (q:=χ) (d:=0) q hP b ho hg' hΓ hn hV (1:Grid f) hG.le he hPt hR hE u _ _ (purse_pos _ _ _ (by assumption)) hu hh hj ζ hc hb hM F IΘ L' Θ hf (by assumption) hv hζ hN hx Vb hm₁ hm₂ hm₃ C₁ L0 ht _ (guard_silent χ hG (mul_pos D.guards Rx.p.threshold_pos)) -- arg
end YM.Massive.Poised
