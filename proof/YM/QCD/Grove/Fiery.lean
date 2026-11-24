import YM.QCD.Grove.Tower
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Grove
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun Kites
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J V:Type}{c f:Side}{N n:ℕ}
open Animals
open Flume Orbit Quarry Folding Further.PhysicalPeriodLimitF933 Macrame PhysicalNext.Repeat Deck Meadow
open Pressure ConnectedActivityE6 Blaze King Push.Uniform
open Brick Dust Slide Trio.Sharp
-- layout
variable {C:Side}{D D' w j:ℕ}{d r t t' p p':ℝ}{B:BudgetPoint}
variable (A:C.val=c.val*D)(M:C.val=f.val*D')(P:Gem c N I)(Q:Gem C N J)(S:Gem f N V)(T:Finset I)(T':Finset J)(T₀:Finset V)(g v:Site C→ℂ){b ε:ℝ}
set_option quotPrecheck false
local notation "Δ"=> normal (Deck.divides A) A
local notation "Δ'"=> normal (Deck.divides M) M
variable (ha: LiftQ (normal (Deck.divides A) A) P Q T T' g B w)(hv:LiftQ (normal (Deck.divides M) M) S Q T₀ T' v B w) (ht:SoilB T' Q B w t') (hu:SoilB T₀ S B w t') (hw:SoilB T P B w t')
variable (hm:Quaint (normal (Deck.divides A) A) g)(hf:Quaint (normal (Deck.divides M) M) v)
def riverW (P:BudgetPoint)(w:ℕ)(d:ℝ):ℝ:=(1+w:ℝ)^2*ticketR P w d
variable (hB: Isle su B w c p p')
include ha hv ht hu hB hm hf hw
lemma fusion (hg:0 < t')(he:0<t)(hT: fareG 1 t N ≤ t')(hp:2*(w+1) < f.val)(h:2*(2*w) ≤ f.val)(hξ:0≤d)
    (hQ:∀ W:Positions (Push.Uniform.Primary f su), ‖W‖+2*p<p'→flags B.threshold (Boulevard.actual W)=∅→∀ l:List (Directions su f),l.length≤ B.order→(∀ i∈ l,‖i‖≤ B.threshold)→ ‖leftDerivs ((songT t' ∘ primed T₀ S)- (fun _=>Reggae.baker f N b)) l (Boulevard.actual W)‖≤d) (i:Site C):
    let x:= Macrame.splitter (Deck.divides A) i
    let s:=w+(2*w+1)
    Woven x (neighbors s x) B t (orchid T P x) (riverW B w d):=by
    intro x s; let Y:= Macrame.splitter (Deck.divides M) i; let e:= Deck.reverts M i; let Z:= closeQ (N:=N) Δ g v e
    let X:=neighbors w x; let F:= orchid T P x
    have heq:∀ (U:Grid c),flags B.threshold U=∅→ F U= Z (orchid T₀ S Y (shapeL h x Y U)):=by
        intro U hx
        have hh:Healthy B.threshold (neighbors w x) U:=by unfold Healthy; rw [hx]; simp
        let W:= shapeL h x Y U
        have hr : 2*(w+1) < C.val := ((hB.cipher).trans_le (le_trans (Nat.le_mul_of_pos_right c.val (Nat.pos_of_ne_zero (show D≠0 from (fun he=>by have h:= C.pos; rw [A,he,Nat.mul_zero] at h; omega)))) A.symm.le)) -- ill inferred U V
        have hxV: Agrees (Lattice.box w) (expandAt i ((Δ).links U)) (expandAt i ((Δ').links W)):=by rw [Slide.rolls,Slide.rolls]; exact (fun p hi h=> (Trio.Sharp.hearth _ x Y U p hi h).symm)
        exact resorts _ _ P Q S T T' T₀ g v ha hv ht i U _ hx (Trio.Sharp.flare h x Y U hh) (Slide.readNear i hr hxV) hf e (fun y hy=> Deck.same_site M i (neighbors w i) (by omega) (Subset.refl _) y hy)
    have hZ : X ⊆neighbors s x:= fun i hi=> (neighbors_mem ..).2 (((neighbors_mem ..).1 hi).trans (Nat.le_add_right ..))
    have hg' : ∀ U,Gated X (F U):= (wind _ _ hw (1:Grid c) x (AnalyticBridge.VerifiedReset.flat_ok ..)).2
    have hM U (h: Healthy B.threshold X U):Push.Local.Chart B.order F U:=(wind T P hw _ _ h).1
    refine ⟨fun i j hh=> mintL _ _ hw _ i j (agrees_mono hh (coe_subset.mpr hZ)),fun i=>gateMon _ _ hZ _ (hg' _),fun i hh=> hM i (hh.mono_left hZ),fun U H l hl hx=>?_,(buds x N).continuous.measurable.comp (notes _ _ hw).1,(by unfold riverW ticketR; positivity)⟩
    have hc : Gated X (leftDerivs F l U):=gatedL (C_:=⟨x,X,halo_subset _ _ (mem_singleton_self _)⟩) hg' l U
    apply (senCamp (n:=w) (neighbors w x) (o:=x) (fun i hi=> (separation_comm ..).trans_le ((neighbors_mem ..).1 hi)) (leftDerivs F l U) he hc).trans; apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ (1+w:ℝ)^2)
    let Z':=token c N t (leftDerivs F l U); obtain ⟨L,hL,hL'⟩:=exists_dual_vector'' ℝ Z'; have hh :L Z' =‖Z'‖:=hL'
    let X':=L.comp (token c N t); let H':= X' ∘ F; let M':= (X'.comp Z) ∘ orchid T₀ S Y
    have heV V (ht:flags B.threshold V=∅): Push.Local.Chart B.order M' V:=(X'.comp Z).contDiff.contDiffAt.comp 0 ((wind T₀ S hu V Y (by unfold Healthy; rw [ht]; simp)).1)
    -- size H' via L depends Z' = Grass x or contour? check token type. songT outputs EvenA
    have he' :∀ X,‖(X'.comp Z) X‖ ≤ ‖token f N t X‖:=by
        intro X; change ‖L _‖ ≤ _; apply (L.le_opNorm _).trans; apply (mul_le_of_le_one_left (norm_nonneg _) hL).trans; change ‖token c N t (streamL (Δ).cut g N (streamL e (star ∘ v ∘ e) N X))‖≤_; exact (offer_boom _ _ _ (fun i=>by rcases hm.sign i with H|H <;> rw [H]<;>simp) _ he).trans (offer_boom _ _ _ (fun i=>by change ‖star (v (e i))‖=1; rcases hf.sign (e i) with H|H<;>rw[H]<;>simp) _ he)
    have hA: Healthy B.threshold X U:=H.mono_left hZ
    change ‖Z'‖≤ _; rw [← show ‖L Z'‖=‖Z'‖ from (by rw [hh,Real.norm_of_nonneg (norm_nonneg _)]),show L Z'=leftDerivs H' l U from ?_]; rotate_left
    · exact (left_linear X' l (hM _ hA) hl).symm -- mismatch token
    exact Trio.Sharp.sapling hB h x Y H' M' (fun a b h=>congr_arg X' (mintL T P hw _ _ _ h)) (fun i hi=>congr_arg X' (heq _ hi)) heV U H (X'.contDiff.contDiffAt.comp 0 (hM U hA)) (fun V hx hz=> gild V (primed T₀ S) b Y (X'.comp Z) he hg hT (notes _ _ hu).2.1 hz hx (mint T₀ S hu) he' hQ) l hl hx
end YM.QCD.Grove
