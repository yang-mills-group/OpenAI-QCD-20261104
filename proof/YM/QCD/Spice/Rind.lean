import YM.QCD.Spice.Cotton
import YM.QCD.King.Stone
/-! # Prices for ψ comparison operator. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Spice
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run Jets
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.AbsoluteSums Footprint Trees
open Sun Cove.Fj Jets.Touch MeasureTheory
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {F k j:ℕ}{c f: Side} {δ q κ a u v η ξ x y w t b':ℝ}{l b:ℕ}{G:Flight j k}{h:f.val=c.val*G.L.val}
local notation "S"=> sliceL G h
variable {T:Grid f→Sheet f}(P:Sun G c f h δ v q u a l T)
open Dust Stew Brick Garden Sway OrbitG Revolve
variable {σ σ' ζ K D μ B₀ m τ γ Λ Λ' :ℝ}
-- paint REAL.Bill on word hue α minus γ; Paid over support.W.K.Piece MUCH future. every F arbitrary. do not charge Jacobian gauge F.L.
variable {E J: Type} [Countable E] [Countable J]
variable (H:Rise f F E J)(I:BudgetPoint) (s:Finset (Fj (Tr f) E J)) (i:E)
set_option quotPrecheck false
local notation "D₀"=> P.equip F b
local notation "A'"=> H.row i
local notation "o'"=> (H.row i).site
local notation "M"=> coreW D₀ H s
variable {p d₀ Ω :ℝ}
abbrev Worth (q:E)(m: BudgetPoint)(a τ:ℝ):Prop:= Woven (H.row q).site (H.row q).support m a (H.main q) τ
lemma leafSub (hh:leftE s={i}): (H.row i).support ⊆ coreW (P.equip F b) H s:= by
   intro j hj; have hx:i∈ leftE s:=by rw [hh]; simp
   exact mem_biUnion.mpr ⟨Sum.inr (.inl i),by simpa [leftE] using hx,hj⟩
-- regular scalar in two charts.Old main vs its own extension.
abbrev lensQ (p: Site f)(N:ℕ)(L: Crate f N→L[ℝ]ℝ): EvenA f N→L[ℝ]ℝ:= ContinuousLinearMap.comp L (((light (Keys f N)).toLinearMap.toContinuousLinearMap).restrictScalars ℝ)
abbrev prismQ (L':Crate c F→L[ℝ]ℝ)(X:Grid f):EvenA f F→L[ℝ]ℝ:= ContinuousLinearMap.comp (lensQ 0 F L') ((roundV (P.equip F b) H X s).restrictScalars ℝ) -- notation may stuck. phase supplier.
variable (hp: Peak (P.equip F b) I.threshold x y ξ (fun i=> Real.exp 1*terra P F b x y i))
variable (he:H.Wave I.threshold) (hh:leftE s={i})(hk:spent s=∅)
variable (hv:Worth H i I x τ)
variable (Q:Crate c F→L[ℝ]ℝ)(hw:rootBill ((sliceL G h).parent (H.row i).site) y Q)
variable (W:Grid f)(hW:Healthy I.threshold (brimW (P.equip F b) H s) W)
-- no existential Heavenly scores, budget global. nonshort tighten factor. Δ W at representatives. Projection of derivative FULL gauge f1. Lens derivative Museum characters? input Uses OK.
variable (z:ℕ)(hz:∀ i' ∈(halo b (coreW (P.equip F b) H s)).image (sliceL G h).parent,separation i' ((sliceL G h).parent (H.row i).site) ≤ z)
open PhysicalNext.JointLoad MultiNext.SignedSource
include hw hv hh
private lemma stretchR (Y:EvenA f F →L[ℝ]ℝ)(hy: ∀ z, Gated (H.row i).support z → ‖Y z‖ ≤ Λ*Sen (H.row i).site x z)(hp:0≤Λ): let Z:=brimW (P.equip F b) H s; let r:= Y ∘ H.main i; LocalOn Z r ∧ Ease.Charm I Z r ∧ I.supBounds (H.row i).site Z r (Λ*τ) ∧ Measurable r :=by
    intro X q; have hX:(H.row i).support⊆ X:=Subset.trans (leafSub P H s i hh) (native_sub D₀ H _)
    have ht:= Woven.stretches hv hX le_rfl; have hm:= (show Ease.Charm I X (H.main i) from ⟨ht.room,ht.use⟩).scales Y; refine ⟨hm.sites,hm,⟨mul_nonneg hp hv.travel,?_⟩,Y.continuous.measurable.comp hv.Borel⟩
    intro V h l hl hL; rw [Push.Local.left_linear Y _ (ht.use _ h) hl]
    exact (hy _ (ConnectedActivityE6.Blaze.King.gatedL hv.gated _ _)).trans (mul_le_mul_of_nonneg_left (ht.pole _ h _ hl hL) hp)
include hp he hk hW hz
lemma songbook (hv':0 ≤ u) (ht:y*fingers F*q ≤ ξ*x) (hc:∀ i,terra P F b x y i≤1) (U:Grid f) (hU:Healthy I.threshold (brimW (P.equip F b) H s) U) (hh':beamAt (brimW D₀ H s) U W w)(hA:0 ≤ w)(hκ:w<δ/2):
    let Y:=prismQ P H s Q W (b:=b); let X':=hue D₀ H I.threshold s; let m:=∏ i∈ops s,(Real.exp 1*terra P F b x y i); let j:= w/(δ/2); let Z':=((1+(z:ℝ))^2); let K:= Y ∘ H.main i; let t:= τ* (Real.exp τ)
    Ease.Charm I (brimW D₀ H s) K ∧ I.supBounds (H.row i).site (brimW D₀ H s) K ((Z'*m)*τ) ∧ Measurable K ∧
    ‖Q (X' U).val-K U‖ ≤ Z'*((m*τ) * (t+(((hooks (F:=F) (sliceL G h) M).card:ℝ)*(ξ*j)+(ops s).card*j))) :=by
    intro Y X m j Z' K t
    have hm:0≤ m:=prod_nonneg fun i _=> (hp.spare i U).nn
    have hp' i' (h:Gated (H.row i).support (i':EvenA f F)): ‖Y i'‖ ≤ Z'*m*Sen o' x i':=by
       have hh':= gateMon (H.row i).support M (leafSub _ _ _ _ hh) i' h
       let Zz:= roundV D₀ H W s; have hQ:= gateR D₀ H s W _ hh'
       apply (hw _).trans ((shard _ _ z hz (Zz i') hp.cup hQ).trans ?_); apply (mul_le_mul_of_nonneg_left ((rounding D₀ H s W hp hW _ hh').trans (mul_le_mul_of_nonneg_left (Stew.shot (Stew.lens o') _ _ hp.bud) hm)) (sq_nonneg _)).trans_eq; change Z' * (m * Sen o' x i')=Z' * m * Sen o' x i'; ring
    obtain ⟨hQ,hK,hL,hX⟩:= stretchR P H I s i hh hv Q hw _ hp' (mul_nonneg (sq_nonneg _) hm); refine ⟨hK,hL,hX,?_⟩
    have h:= onHealthy D₀ H s U hU hh; let i':=H.main i U; have hτ: Sen o' x i' ≤ τ:=(hv.stretches (Subset.trans (leafSub P H s i hh) (native_sub D₀ H s)) le_rfl).sizeU U hU
    have htC: load (fun _=>x) (light _ (H.reading I.threshold U i))≤τ:=h.symm ▸ (Stew.shot (Stew.lens o') _ _ hp.bud).trans hτ
    obtain ⟨hU',hC⟩:= sparkler H U W P s hp hv' ht hc hh hk he hW hU hh' hA hκ htC
    let Zz:= roundV D₀ H W s (H.reading I.threshold U i)
    let g:= X U
    rw [show K U= Q Zz.val from (by change Y (i')=Q Zz.val; unfold Zz; rw [h]; rfl), ← map_sub]
    apply (hw _).trans; apply (shard _ _ z hz (g-Zz) hp.cup hU').trans
    unfold t; rw [mul_comm τ (Real.exp _)]; exact mul_le_mul_of_nonneg_left hC (sq_nonneg _)
-- shrink γ for any ops_empty via full pre budget; wage not plank ext. dry plus.
omit he hk hz
lemma grandR (p':ℝ) (he: Sea G h b δ p' q I.threshold P.Z P.V 2) (hm:ops s=∅)(hh':4*((fingers F*p')*y)≤ x/4):
    I.supBounds (H.row i).site (brimW D₀ H s) (prismQ P H s Q W (b:=b) ∘ H.main i) τ :=by
     let T:= (D₀).shortP W
     have hq i (hi:i∈limits M): amount T i S ≤ fingers F*p':= freezeQ P i W b 2 p' he (hW.mono_left (by rw [brim_eq]; exact Corona.halo_mono (le_refl _) (singleton_subset_iff.mpr (mem_filter.mp hi).2)))
     let J:= prismQ P H s Q W (b:=b); have hz v (h':Gated (H.row i).support (v:EvenA f F)): ‖J v‖≤ 1*Sen o' x v:=by
        let K:= roundV D₀ H W s v; rw [one_mul]
        apply (hw (light _ K)).trans; unfold K; rw [stampF,show axle D₀ W s=1 by simp [Cove.axle,hm],ContinuousLinearMap.one_apply, echo S]; exact petals _ _ (light _ v) (gateMon _ M (leafSub P H s i hh) _ h') hq hp.cup hh' hp.bud
     simpa only [one_mul] using (stretchR P H I s i hh hv Q hw J hz zero_le_one).2.2.1
end YM.QCD.Spice
