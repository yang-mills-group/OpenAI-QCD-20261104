import YM.Cape.Mem
import YM.Play.Lair
import YM.Extra.MULTISOURCE_BOUNDS.Inheritance
import YM.Play.Firs
import YM.Play.Quiet
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Apron
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{β τ C μ W:ℝ}
variable {R:Rep su f}{O:BudgetPoint}{F:Tree.Forest S.ratio}{Q:Target su P}{o:Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι κ I E J D:Type}{N:ℕ}
variable {j k m i k₁ n:ℕ}
variable {z η p h a a' hQ v δ b s u q:ℝ}{P' : Plan k}{X:Run.St f}
variable (L':Flight j k)(d:f.val=c.val*L'.L.val)(K:KernelChoices)
local notation "S'"=> Flight.visit L' K d
variable {T:Tube su (Flight.visit L' K d)}{W' :ℕ→Atom su 2}
variable (H:Cash W τ μ L'.L Q o C T (trimP T O δ β b))
variable {P₀:Rise f N E J} [Countable E][Countable J]
variable (G:Sun L' c f d η h z a a' m X) (U :Swathe L' d X W' P' h η a u v i)
variable (Γ:Land c (Site c) (Site c)){D':Pays c (Site c) (Site c)}
variable [Fintype I] (Y:Stitch.Tablet P₀ I)(A:I→Site f)(φ:ℝ)
local notation "M"=> Ribbon.ample N I
local notation "R'"=> trimP T O δ β b
local notation "B"=> radiusB τ
local notation "M'"=> highR L τ
local notation "Z'"=> G.equip N (radiusB τ)
local notation "Zⁱ"=> QCD.Jets.Touch.roof (G.equip N (radiusB τ)) P₀ 30 B
local notation "Y'" => closet H (G.equip N (radiusB τ)) (Zⁱ) Y A φ
local notation "U'" => loommark I (VarnC H U N)
local notation "X'" => loommark I (sailP H Γ N)
local notation "Vx" => tableau L' d K P₀ H G U Γ
local notation "Tx"=> vantage L' d K H G U Γ Y A φ
local notation "Uq"=> deckHue H (Z') P₀ (Zⁱ)
open Anomaly Play Chamber Camp Cupola
open Stitch Stitch.Tablet
local notation "Ip"=> Wound Zⁱ
local notation "X0"=> Keys f N ⊕ Spine I
local notation "X1"=> Keys c N ⊕ Spine I
local notation "K0"=> Keys f N
local notation "K1"=> Keys c N
variable {m₁:ℕ}
namespace Grove
-- degree on arbitrary subsets.D
set_option quotPrecheck false
local notation "Pe" e=> Fj.pin (picksV f m (radiusB τ)) e (∅:Finset J)
local notation "lk"=> (S').ratio.parent∘ A
local notation "T0"=> (withdraw N ((S').ratio.parent ∘ A) φ)
local notation "Oi"=> omegaE Zⁱ Y (fun (_:Varn f c ⊕ Gaze c)=> ∅)
local notation "inH" => (united U' X')
local notation "sM"=> (swingE N (Tx) (Oi))
variable (e:Finset E)(Z:Finset I)
variable {q₀:I→Bool} {θ α:ℝ}
variable (χ:Chi)(V:Grid c)(p':Wound (roof (G.equip N (radiusB τ)) P₀ 30 (radiusB τ)) ⊕ Varn f c⊕Gaze c →ℝ)
variable (hF:Registry L' d K H G U Γ Y A φ p' θ α q₀ χ)
variable (hR: Fleet.Regal N ((Flight.visit L' K d).ratio.parent ∘ A) φ q₀ (vantage L' d K H G U Γ Y A φ) (Sum.elim (fun w=>Y.markers w.val) (fun _=>∅))) -- Aura bargain
variable (hE:∀ i∈ e,(Y.spine i).Nonempty)
open MassiveQCD.Cape MassiveQCD.Plate
variable (Mz:Clusters (vantage L' d K H G U Γ Y A φ).Bright→RegularAddress c)
variable (hM:∀ i,(Mz i).support=GasP.seatP (vantage L' d K H G U Γ Y A φ).lightF i)
variable (Tq:Set (Finset I))(Tτ: Finset (Finset I)) (u₁:ℝ)(d0 r:ℕ)
-- Tτ single tile masks; can also post for empty inputs but Lens only admits Nonempty. d0 B enough from later calibration permits.
local notation "Bt"=> crude Tx χ Mz
local notation "Ta"=> Reel.Answer N lk Bt sM Tq
local notation "Xᴿ"=> Reel.render N lk φ u₁ Bt sM Tq
local notation "Vq"=>Pressure.temp τ
local notation "Rp"=> Ray lk (r+45*radiusB τ)
local notation "Rsg"=> Tτ -- notation
-- standalone in row geometry for bound needed.We.Fires arbitrary before.H marker card.Power.
noncomputable abbrev parish (o:I→Site c)(Tτ:Finset (Finset I))(m:ℕ) := {V: Finset I// V∈Tτ ∧ Ac.Spark (Ray o m) V }
local notation "Is"=>parish lk Tτ (r+45*B)
instance (o:I→Site c)(Tτ:Finset (Finset I))(m:ℕ):Fintype (parish o Tτ m):=by unfold parish; infer_instance -- noncomputable by section.
noncomputable def rayA (o:I→ Site c)(Tτ: Finset (Finset I))(r b:ℕ)(i:parish o Tτ r): RegularAddress c:= let y:=o i.property.2.1.choose; ⟨y,halo b {y},halo_subset _ _ (mem_singleton_self _)⟩
local notation "Vt"=> Varn f c⊕ Gaze c
noncomputable abbrev Zeal (Z:Finset I)(t:Clusters (Tx).Bright) := (sM) t=Z ∧ ∀ j,front Zⁱ (S') (Varn f c ⊕ Gaze c) (Pe (fled Y e Z)) (t.2 j).val -- use prel bind♢
local notation "PR"=> Zeal L' d K H G U Γ Y A φ e
-- oper shields.Mtx no need include all Tq. choose via per-mask subset. Lens.Mark.F.V even cells overlap.
noncomputable def horn (j:Ta): Option Is:=if h:(sM) j.val∈Tτ ∧ Ac.Spark (Rp) ((sM) j.val) ∧ (PR) ((sM) j.val) j.val then .some ⟨_,h.1,h.2.1⟩ else .none
local notation "SX"=> horn L' d K H G U Γ Y A φ e χ Mz Tq Tτ r -- reorder.
variable {d₁:ℕ}
noncomputable def assembly: Lake (c:=c) (I:=I) (J:=Ta) (parish lk Tτ (r+45*B)) Vq:=⟨rayA lk Tτ _ d0,Subtype.val,SX⟩
local notation "Aq"=> assembly L' d K H G U Γ Y A φ e χ Mz Tq Tτ d0 r
include hE hF hM hR
lemma reaping (Z:Finset I)(i:Clusters (Tx).Bright)(h:game L' d K H G U Γ Y A φ e χ Z V i≠0) : ∃ (hj:Z.Nonempty ∧ Z.image lk⊆ (Mz i).support), (PR) Z i:=by
    obtain ⟨hp,hk,hx,hG⟩:= aurea L' d K H G U Γ Y A φ e Z χ V p' hF hR hE i h
    unfold game Play.Camp.port at h; split at h; swap; · exact (h rfl).elim
    next hα=> split at h
              next hb=> exact ⟨⟨hp,(hM i).symm ▸ hk⟩,⟨hα.2,hb⟩⟩ -- use And not exists prop?
              next hb=> exact (h rfl).elim
lemma postage (j:Ta) : Reel.mist Xᴿ Vq j V= turn I u₁ (T0 ((Tx).honest χ V j.val)) :=by
    rw [Reel.currentS]; let v:=literal_color (Tx) Mz χ hM hF.favorable (fun k=> hF.color.warp k) j.val V; exact congr_arg (fun x=> turn I u₁ (T0 x)) v
lemma hungry (j:Ta)(V':Finset I)(he: PR V' j.val) : turn I u₁ (T0 (game L' d K H G U Γ Y A φ e χ V' V j.val))= Reel.mist Xᴿ Vq j V:=by
    rw [postage L' d K H G U Γ Y A φ e χ V p' hF hR hE Mz hM Tq u₁ j,game,if_pos ⟨he.1 ▸ j.2.2.1,he.1⟩,Play.Camp.port,if_pos he.2]; rfl
omit hF hM hE hR
lemma audible (Z:Is)(j:Ta) : SX j= .some Z↔ PR Z.val j.val:=by
    unfold horn; split
    next he=>
        constructor
        · intro hk; obtain rfl:=Option.some.inj hk; exact he.2.2
        intro hp; exact congr_arg _ (Subtype.ext hp.1)
    next he=>
        refine ⟨nofun,fun hp=>False.elim (he ⟨hp.1.symm ▸ Z.2.1,hp.1.symm ▸ Z.2.2, hp.1.symm ▸ hp⟩)⟩ -- `nofun` danger?
include hE hF
variable (hr:∀ j∈ e,∀ i∈ Y.spine j, ((P₀.row j).support.image (sliceL L' d).parent)⊆ Ray ((Flight.visit L' K d).ratio.parent ∘ A) r i)
include hr
lemma fullBar (i:Clusters (Tx).Bright)(V:Grid c)(j:Finset I)(ht: game L' d K H G U Γ Y A φ e χ j V i ≠0): Ac.Spark (Rp) j ∧ GasP.seatP (Tx).lightF i ⊆ j.biUnion Rp:=by
    let v:=Pe (fled Y e j); have hz:∀ k∈leftE v,(Y.spine k).Nonempty:= fun k hk=>by unfold v at hk; rw [pinX] at hk; exact hE _ (mem_filter.mp hk).1
    unfold game at ht; split at ht; swap; · exact (ht rfl).elim
    next he=>
       have hw:= prick L' d K G Y A (fled Y e j) hF.room.2 (fun i hi k hk=> hr i (mem_filter.mp hi).1 k hk)
       rw [← he.2]; exact Camp.rawP H Z' Zⁱ Y A φ (united U' X') hF.property ((roofs Z' P₀ 30 B le_rfl hF.room.2).1) v χ V hz (pinK ..) hw i hF.favorable (fun _=>∅) ht -- shadow
-- needed geometric margin forall Z.Power.W Pay
local notation "r!"=> (r+45*B)
variable (hm:∀ s∈Tτ,s.card≤ d₁)(hk:d₁*(2*(r+45*radiusB τ))+(r+45*radiusB τ)+4 ≤ d0)
omit hF hE hr
include hm hk
lemma league (j:Is)(i:I)(hp:i∈j.val): separation ((Aq).addr j).site ((lk) i) ≤ d₁*(2*r!):= (ridgeSpan lk j.val _ j.2.2 _ i j.2.2.1.choose_spec hp).trans (Nat.mul_le_mul_right _ (hm _ j.2.1))
include hF hE hr hR hM
set_option linter.unusedSectionVars false in
lemma memberP : Lake.Pillar lk Xᴿ Aq:=by
    refine ⟨fun i=>i.2.2.1,?_,?_,?_⟩
    · intro i j hj; obtain ⟨p,hp,rfl⟩:= mem_image.mp hj; exact halo_spec.mpr ⟨_, mem_singleton_self _,le_trans (league L' d K H G U Γ Y A φ e χ Mz Tq Tτ d0 r hm hk i p hp) (by omega)⟩
    · exact fun i j he=> ((audible L' d K H G U Γ Y A φ e χ Mz Tq Tτ r j i).mp he).1
    intro i j he; by_cases hW: Reel.mist Xᴿ Vq i=0; exact Or.inr hW; push Not at hW; left
    have hg:∃ V,Reel.mist Xᴿ Vq i V≠0:=by by_contra! hn; exact hW (funext hn)
    obtain ⟨V,hv⟩:= hg
    have hi:game L' d K H G U Γ Y A φ e χ j.val V i.val≠0:=fun h=> hv (by rw [← hungry L' d K H G U Γ Y A φ e χ V p' hF hR hE Mz hM Tq u₁ i j.val ((audible L' d K H G U Γ Y A φ e χ Mz Tq Tτ r j i).mp he),h,map_zero,map_zero]); intro z hz
    obtain ⟨w,hx,hg⟩:= halo_spec.mp (Extra.Multi.System.within _ hz); obtain ⟨p₁,hp,h⟩:= mem_biUnion.mp ((fullBar L' d K H G U Γ Y A φ e χ p' hF hE r hr _ V _ hi).2 ((hM i.val) ▸ (show w∈(Mz i.val).support from hx)))
    let X:= ((Aq).addr j).site; have hf:r+45*radiusB τ=r!:=rfl
    refine halo_spec.mpr ⟨X,mem_singleton_self _,?_⟩; have hk₀: separation X ((lk) p₁) ≤ _:= league L' d K H G U Γ Y A φ e χ Mz Tq Tτ d0 r hm hk j p₁ hp; have he:separation ((lk) p₁) w ≤ r+45*radiusB τ:= (portion _ _ _ _).mp h; exact (separation_triangle X w z).trans (le_trans (Nat.add_le_add ((separation_triangle X ((lk) p₁) w).trans (Nat.add_le_add hk₀ he)) hg) hk)
end Grove
end YM.MassiveQCD.Apron
#print axioms YM.MassiveQCD.Apron.Grove.memberP
