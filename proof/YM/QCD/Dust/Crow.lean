import YM.QCD.Dust.Guide
/-! # ordered chart germ payout along the lifted spin phase. Does NOT assume spin-star in this frame. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Dust
open Function Filter Set Lattice Wilson Pressure RG Precision Tree Next Next.SectorChange Next.Fluctuations Next.Foundations
    Exterior Bloch Bid Push.SectorMeasure MultiNext.SignedSource MultiNext.SignedSource.Banjo Planned.AtomRegular MeasureTheory Analysis
open AnalyticBridge.SectorAffine.Offset WardBin.Lies PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Lat Kit Grass Brick Cove Stew
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {c f : Side} {S : StepData c f} {T : Tube su S} {Pt : Teller su} {k : S.Choices} {V : Config su c} {F : Forest S.ratio} {L:Side}
    {P B : BudgetPoint} {o : Site f} {g : Site c → su.El} {X : Support f} {Y : Support c} {Q C M r t x τ W w σ G₀ ρ : ℝ} {I : Type} {J: BudgetPoint}
    {A : Stores S} {n l N : ℕ} {D : Slab su c l} {q : Chi} {d u : ℝ} {f' : Config su f → ℝ} {H:Grid f→EvenA f N}
-- receiving kit B jets.Ep
lemma plumes {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{g:Grid f→E} (hp: Ease.Charm B X g){U:Grid f}{x:Directions su f}(he:Healthy B.threshold X (increment U x)): ContDiffAt ℝ (↑B.order) (g ∘ increment U) x:=by
   obtain ⟨hz,hy⟩:= Lyre.arisen X x
   let A:=g ∘ increment (increment U x); let L:=Lyre.surge X x; let E:= (g ∘ increment U)
   have hA:ContDiffAt ℝ (↑B.order) (A ∘ L) 0:=by refine ContDiffAt.comp (f:=L) 0 ?_ (hy.of_le le_top); rw [show L 0=0 from hz]; exact hp.smooth _ he
   have hh(i:Edge (Site f)):∀ᶠ v: Directions su f in 𝓝 0,su.lieExp (x i+ v i)=su.lieExp (Lyre.gust _ (x i) (v i))*su.lieExp (x i):=(continuous_apply (A:=fun _:Edge (Site f)=>su.Color) i).continuousAt (x:=(0:Directions su f)) |>.eventually (Lyre.slip _)
   have hx :A ∘ L =ᶠ[𝓝 0] fun v=> E (x+v):=by filter_upwards [Filter.eventually_all.mpr hh] with v hv; apply Eq.symm; refine hp.sites _ _ (fun i hi hl=>?_); simp only [L,Lyre.surge,increment,if_pos (show Mom.needed X i from ⟨hi,hl⟩),Pi.add_apply,hv,mul_assoc]
   have hp : ContDiffAt ℝ (↑B.order) (fun v=> E (x+v)) (x-x):= (sub_self x).symm ▸ (hA.congr_of_eventuallyEq hx.symm : ContDiffAt ℝ _ (fun v=> E (x+v)) _)
   have ht:= hp.comp (f:=fun v=>v-x) x (contDiffAt_id.sub (contDiffAt_const (c:=x))); rw [show (fun v=>E (x+v)) ∘ (fun v=>v-x)=E from funext fun i=>congr_arg E (add_sub_cancel ..)] at ht; exact ht
set_option linter.unusedSectionVars false
variable (Z:Hera.Rights su n) (a : Museum F x A X Y I) [Fintype I] (hq: Walled S X Y x l) -- l used Slab, remove later
    {C₀:Libretto su n}{D':Record}
    (hp : Plays C₀ D' P B Pt T x) (hg : Canvas P (S.ratio.parent o) (reach x) V g n C₀.C)
variable (hz: Short S B X)(hk:5 ≤ n)(ho:o∈ X)(hV:Healthy P.threshold Y V)(U:Grid f) (Ω : Prices su I) (hu:0≤ u)(he:u*‖tape Ω‖ ≤ D'.ε*B.threshold) (hl:l ≤ n) (hD:∀ i,P.dirBound (S.ratio.parent o) (D i))
include hp hg hz hk ho hV hu he hl hD
set_option quotPrecheck false
local notation "X₀"=> enters V (S.ratio.parent o) (reach x) g D (a.extra g u Ω)
local notation "Φ"=> (display T F x k true ∘ (X₀))
local notation "K"=> S.patch.L
local notation "Kₜ"=> C₀.M + tranche S.patch.L n D'.Q (loom P (reach x) C₀.C) (u*‖tape Ω‖) B.threshold
section
variable (k q d) -- shadow probe df
include d q k U
lemma chordD : ContDiffAt ℝ n (display T F x k true ∘ enters V (S.ratio.parent o) (reach x) g D (a.extra g u Ω)) 0 ∧ (let y:= display T F x k true ∘ enters V (S.ratio.parent o) (reach x) g D (a.extra g u Ω);
       Promise 2 (Kₜ) (fern K) B o X (y 0) ∧ (∀ e, Mom.needed X e → ‖y 0 e‖ ≤1 ∧ Lyre.width B o e ≤ 1) ∧ (∀ t∈ Set.Icc (0:ℝ) 1, Healthy B.threshold X (increment 1 (t • y 0))) ∧
       ∀ i, 1≤ i→ i ≤ n → ∀ v:Fin i→Panels l,(∀ i,‖v i‖ ≤1) → Promise 2 (Kₜ) (fern K) B o X (iteratedFDeriv ℝ i y 0 v)) :=by
    let b:=a; have ht:=hp.rehearsed; have hU':= he.trans ht.tensions.noise
    have hw' := (a.extra_size g u hu Ω).trans hU'
    have hy := ht.tensions.small.trans (min_le_right ..)
    have hU := border_healthy hp.sew C₀.width C₀.price ht.early (hp.acts F k) D'.majorant (by omega) ht.tensions a hp.bulletin C₀.Z rfl ht.wire hp.space ht.temp_eq hV U Ω hu he B.threshold_pos (q:=q) (d:=d)
    obtain ⟨he',hz'⟩ := plucked a hp.bulletin ht.weft (hp.acts F k) hz hg ho C₀.C_one ht.tensions.allows U Ω hw' D D'.majorant (by omega) hy hU
    have hE':= le_trans (le_mul_of_one_le_left ((mul_nonneg hu (norm_nonneg _)).trans hU') D'.majorant) hy
    have hh := (timesEnter hg (hp.acts F k) ht.temp_eq (by omega) hD C₀.C_one hl D'.majorant hE' ht.tensions.allows.le hw' true).1
    have h j (hj:j≤n) := first_promise (X:=X) (hp.stages F) hg ht.tensions.coarse ht.temp_eq ht.powers C₀.C_one hl hD hE' (hp.acts F k) D'.majorant C₀.matins (by omega) ht.tensions.allows.le hw' (a.extra_size g u hu Ω) hj
    refine ⟨hh, ?_,he',hz',fun i _ hi=> h _ hi⟩
    simpa only [iteratedFDeriv_zero_apply,fern] using h 0 (Nat.zero_le _) 0 (by simp)
include Z
lemma inStep (hQ : Woven o X B W H τ): let z:Panels l → Directions su f:=display T F x k true ∘ (X₀)
    let Q := (wash o N W) ∘ H
    Through n (Q ∘ increment (1:Grid f) ∘ z) 0 (patterns n*((3*(Kₜ))^n*Z.fee*τ)):=by
    intro z Q; have hL': 1≤ Kₜ:= le_trans C₀.matins (le_add_of_nonneg_right (tranche_nn _ _ (zero_le_one.trans D'.majorant) (mul_nonneg hu (norm_nonneg _)) B.threshold_pos.le)) -- precedence notation Kt
    obtain ⟨hj,hj',hs,hx,hA⟩:= chordD k q d a hp hg hz hk ho hV U Ω hu he hl hD -- order?
    let ζ:= Q ∘ increment (1:Grid f); have hX: Healthy B.threshold X (increment 1 (z 0)):=by simpa only [one_smul] using hx 1 (by simp)
    have hσ : ContDiffAt ℝ n ζ (z 0):= by
       let p: Ease.Charm B X H:= ⟨hQ.room,hQ.use⟩
       exact (plumes (p.scales (wash o N W)) hX).of_le (Nat.cast_le.mpr hp.rehearsed.orders)
    have hη:=Z.large; have he₀:=hQ.travel; refine ⟨hσ.comp (f:=z) _ hj,fun i hi=>?_⟩
    apply slots_bound (G:=ζ) hj hσ hi (by positivity : 0 ≤ (3*(Kₜ))^n*Z.fee*τ); intro p v hv
    let b (i:Fin p.length):= iteratedFDeriv ℝ (p.partSize i) z 0 fun j=> v (p.emb i j)
    let q:=iteratedFDeriv ℝ p.length ζ (z 0); obtain ⟨g,hg,h⟩:= commune (X:=q b)
    let M:= g.comp (wash o N W); let P':= M ∘ H
    have hx z: ‖M z‖ ≤ 1*Sen o W z:= (g.le_opNorm _).trans (mul_le_mul_of_nonneg_right hg (norm_nonneg _))
    have hM: B.supBounds o X P' τ:= by rw [← one_mul τ]; exact breath hQ hx zero_le_one
    have hb:∀ i,Lyre.Sized (3*(Kₜ)) (b i) B o :=by
       intro i; let u₀:=(Kₜ); have hK:1≤u₀:= by assumption
       have hf:= (hA _ (p.partSize_pos i) ((p.partSize_le i).trans hi) (fun j=> v (p.emb i j)) (fun j=>hv _)).shot (fern_pos K).le (fern_one K) (zero_le_one.trans hK); have he:(↑(2:ℕ)+1)*u₀*fern K ≤3*u₀:=by norm_num; exact mul_le_of_le_one_right (by positivity) (fern_one K)
       exact ⟨hf.1.trans he, fun j=> (hf.2 j).trans (mul_le_mul_of_nonneg_right he (Lyre.width_pos ..).le)⟩
    have hf:p.length ≤ n:= p.length_le.trans hi
    change ‖q b‖ ≤ _; rw [h]; have hd: g (q b)= iteratedFDeriv ℝ p.length (P' ∘ increment 1) (z 0) b:= (congr_arg (fun v:Directions su f [×p.length]→L[ℝ] ℝ=>v b) (g.iteratedFDeriv_comp_left hσ (Nat.cast_le.mpr hf))).symm
    rw [hd]; have hc:Ease.Charm B X H:= ⟨hQ.room,hQ.use⟩
    apply (Z.moves 1 (z 0) b _ hf (hf.trans hp.rehearsed.orders) (hc.scales M) hM hX hs hb).trans
    rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith) hf) (zero_le_one.trans Z.large)) hQ.travel
end
end YM.QCD.Dust
