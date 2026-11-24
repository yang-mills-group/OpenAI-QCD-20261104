import YM.Play.Camp
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Play
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon Apron
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{β τ C μ W:ℝ}
variable {R:Rep su f}{O:BudgetPoint}{F:Tree.Forest S.ratio}{Q:Target su P}{o:Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι κ I E J D:Type}{N:ℕ}
variable {δ b:ℝ} (H:Cash W τ μ L Q o C T (trimP T O δ β b)){P₀:Rise f N E J}
variable (G:Send S.ratio N D) (M:Fj D E J→Support c)
variable [Fintype I]
variable (X:Stitch.Tablet P₀ I)(z:I→Site f)(a:ℝ)
local notation "t"=>O.threshold
local notation "M'"=> Ribbon.ample N I
local notation "z'"=> S.ratio.parent ∘ z
local notation "I'"=> Ribbon.Spine I
open Stitch
local notation "Β"=>banknote N z' a
variable (Y:Fleet H κ (ample N I))
local notation "Ξ"=> closet H G M X z a
local notation "Tx"=> united (Ξ) Y
variable {q':I→Bool}(hw:X.Wave O.threshold q' z)(hk:Cove.Count G P₀ M)
namespace Camp
open TabletV
variable (p: Finset (Fj D E J))
local notation "V'"=> Wound M
local notation "P'"=> Piece S (Wound M ⊕ κ)
local notation "p'"=> plume P₀ G M p
variable (χ:Chi)(U:Grid c)
open PhysicalNext.Repeat.Greenbelt
variable (hs : ∀ j∈ leftE p, (X.spine j).Nonempty) (he:spent p=∅)
set_option quotPrecheck false
local notation "H'"=> student H G M X z a Y p hk hw hs he
local notation "Zs"=> campus H G M X z a Y p hk hw hs he
local notation "Ip"=> ↥(plume P₀ G M p)
local notation "Cv"=> month (P₀:=P₀) M G p
include hw hk hs he
private lemma vote (s:Finset Ip)(hv:s∈Cv) :let v := s.image (fun i:Ip=> (H' i).val); (Tx).shellF.legal v∧∀ i∈v,(Tx).shellF.born i:=by
    intro v; refine ⟨⟨?_,?_⟩,?_⟩
    · intro j hj; obtain ⟨k,hk₀,rfl⟩:=mem_image.mp hj; exact (H' k).2.1.2.1  -- hk shadow
    · intro i hi j hj hh; obtain ⟨x,hx,rfl⟩:=mem_image.mp hi; obtain ⟨y,hy,rfl⟩:=mem_image.mp hj; change Disjoint ((Tx).fullA (badge M S κ _)) ((Tx).fullA (badge M S κ _)); rw [partV,partV]; exact (mem_filter.mp hv).2 hx hy (fun h=>hh (congr_arg (fun i:Ip=>badge M S κ (child G M p i)) h)) -- types
    intro j hj; obtain ⟨k,hk₀,rfl⟩:=mem_image.mp hj; exact (H' k).2.1.2.2
omit hw hk hs he
local notation "sp" r=> prism T τ χ o.K U (allot r)
local notation "Sp" r=> planted (prism T τ χ o.K U (allot r)) (∅:Finset (Head S))
-- grasses choose sum stamps
def weald (Ω: Tree.Forest S.ratio)(s: Finset Ip): StampF Ω T (EvenA c M'):= fun V w=>∏ i∈s,(Tx).coming (Sum.inl (child G M p i)) V w
include hw hk hs he
variable (hU: ∀ i:↥(plume P₀ G M p), Healthy (Pressure.temp τ) (i.val.biUnion M) U) (hV:(united (closet H G M X z a) Y).Famous)
include hU hV
lemma arbitration (s:Finset Ip)(hv:s∈Cv):
    (∏ j∈s,(Tx).vF (badge M S κ (child G M p j)) χ U)= choiceS fun r:Reserve S=> draws (Sp r) (weald H G M X z a Y p (allot r) s):=by
    let Γ:=Tx; let cP (i:Ip):=(H' i).val
    let c' (j:Ip):= Sum.inl (β:=κ) (child G M p j); let A:=s.image cP; have hl:= pupil H G M X z a Y hw hk p hs he
    obtain ⟨hy,hM⟩:=vote H G M X z a Y hw hk p hs he s hv
    have hL i (h:i∈A): (i: Finset P').toLeft=∅:=by
        obtain ⟨x,hx,rfl⟩:= mem_image.mp h; change (badge ..).toLeft=∅; ext; simp [badge]
    have hV' i (h:i∈A): Healthy (Pressure.temp τ) (Γ.fullA i) U:=by
       obtain ⟨x,hx,rfl⟩:=mem_image.mp h; change Healthy _ ((Tx).fullA (badge ..)) _; rw [partV]; exact hU _
    have he : ∏ i∈ A,Γ.vF i χ U= ∏ i∈s,Γ.vF (cP i) χ U:=prod_image (Subtype.val_injective.comp hl).injOn
    refine Eq.trans he.symm ((Fleet.GlintV.pureP Γ χ U A hV hy hM hL hV').trans ?_); apply congr_arg choiceS; funext r; apply congr_arg (draws (Sp r)); funext V w
    have hx : A.biUnion id=(∅:Finset (Head S)).disjSum (s.image c'):=by
       ext t₁; simp only [A,image_biUnion,mem_biUnion,id_eq]; constructor
       · rintro ⟨k,hk,hx⟩; rw [mem_singleton.mp (show t₁∈{Sum.inr (c' k)} from hx)]; exact inr_mem_disjSum.mpr (mem_image_of_mem _ hk)
       intro h; rcases t₁ with i|i; · simp at h
       obtain ⟨j,hj,rfl⟩:= mem_image.mp (inr_mem_disjSum.mp h); exact ⟨j,hj,mem_singleton_self _⟩
    refine Eq.trans (b:=(Γ.suitcase (allot r)).capacityP ((∅:Finset (Head S)).disjSum (s.image c')) ∅ V w) ?_ ?_
    · apply congr_arg (fun i=> (Γ.suitcase (allot r)).capacityP i ∅ V w)
      -- via equality per point; no dec inst required
      ext i; rw [← hx]; simp only [mem_biUnion]
    refine Eq.trans (Fleet.GlintV.pure_term Γ _ _ _ _ w) (prod_image ((Sum.inl_injective.comp (childInj G M p)).injOn))

omit hw hk hs he hU hV
-- integrable every shot on derived receipts.
def skyM (Ω: Tree.Forest S.ratio) : StampF Ω T (EvenA c M'):= fun V w=> ∑ s∈Cv, weald H G M X z a Y p Ω s V w
private lemma skyblue {α β:Type*}[Fintype α](s:Finset β)(Y:α→β→EvenA c N): (∑ j∈s,choiceS fun r=>Y r j)=choiceS (fun r=> ∑ j∈s,Y r j):=by
   unfold choiceS; rw [← smul_sum,sum_comm]
variable (r:Reserve S)(k:S.Choices)
local notation "Sp'" k => (planted (prism T τ χ o.K U (allot r)) (∅:Finset (Head S))).taggedL k
include hV
lemma indigo (s: Finset Ip): Integrable (fun v:(allot r).Slice su ×Air f su=>weald H G M X z a Y p (allot r) s ((Sp' k).wrapY v.1) v.2) (((allot r).order su).prod (Sp' k).dice):=by
    let X₀:= Sp' k
    let Vx(i:Ip)(j:(allot r).Slice su × Air f su):=(Tx).coming (.inl (child G M p i)) (X₀.wrapY j.1) j.2
    have hu (i:Ip) : Envelope (Vx i):= Fleet.supremumG (Tx) (X:=X₀) _ hV rfl rfl
    exact envPlot (envCasting s Vx fun i _=> hu i) _ -- s (fun j l=> (Tx).coming (Sum.inl (child G M p j)) ((Sp' k).wrapY l.1) l.2) ?_
lemma cirrus : Integrable (fun v:(allot r).Slice su ×Air f su=>skyM H G M X z a Y p (allot r) ((Sp' k).wrapY v.1) v.2) (((allot r).order su).prod (Sp' k).dice):= integrable_finset_sum _ fun i _=> indigo H G M X z a Y p χ U hV r k i
include hw hk hs he hU
lemma rainV :
    (∑ s∈Cv, ∏ j∈s,(Tx).vF (badge M S κ (child G M p j)) χ U)= choiceS (fun r:Reserve S=> draws (Sp r) (skyM H G M X z a Y p (allot r))):=by
        rw [sum_congr rfl (g:=fun s=> choiceS (fun r:Reserve S=> draws (Sp r) (weald H G M X z a Y p (allot r) s))) (fun i hi=> arbitration H G M X z a Y hw hk p χ U hs he hU hV i hi),skyblue]
        apply congr_arg choiceS; funext r; unfold draws; rw [skyblue]; apply congr_arg choiceS; funext k
        unfold call skyM; exact (MeasureTheory.integral_finset_sum _ (fun i _=> indigo H G M X z a Y p χ U hV r k i)).symm

end Camp
end YM.MassiveQCD.Play
#print axioms YM.MassiveQCD.Play.Camp.rainV
#print axioms YM.MassiveQCD.Play.Camp.cirrus
