import YM.QCD.Dust.June
import YM.Massive.Horizon.Page
/-! Spinful (even pair shelf) cost without flavor symmetry, adapted Dust/{Melody,Peak}. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Dust
open Function Filter Set Lattice Wilson Pressure RG Precision Tree Next Next.SectorChange Next.Fluctuations Next.Foundations
    Exterior Bloch Bid Push.SectorMeasure MultiNext.SignedSource MultiNext.SignedSource.Banjo Planned.AtomRegular MeasureTheory Analysis
open AnalyticBridge.SectorAffine.Offset WardBin.Lies PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Lat Kit Grass Brick Cove Stew ConnectedActivityE6.Blaze Push.Uniform
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {c f : Side} {S : StepData c f} {T : Tube su S} {Pt : Teller su} {k : S.Choices} {V : Config su c} {F : Forest S.ratio} {L:Side}
    {P B : BudgetPoint} {o : Site f} {g : Site c → su.El} {X : Support f} {Y : Support c} {Q M m r t x τ W w σ G₀ ρ v R : ℝ} {I : Type} {J: BudgetPoint}
    {A : Stores S} {n l N j : ℕ} {D : Slab su c l} {q : Chi} {d u : ℝ} {f' : Config su f → ℝ} {H:Grid f→EvenA f N}
variable (Z:Hera.Rights su n)(a:Museum F x A X Y I) [Fintype I] {C:Libretto su n}{E:Record}
    (hp:Plays C E P B Pt T x) (hg :Canvas P (S.ratio.parent o) (reach x) V g n C.C)
variable (hz:Short S B X)(hk:5≤n)(ho:o∈X)(hV: Healthy P.threshold Y V) (U:Config su f)(Ω:Prices su I)(hu:0 ≤u)(hv:u*‖tape Ω‖ ≤ E.ε *B.threshold) (hl:l ≤ n) (hD:∀ i,P.dirBound (S.ratio.parent o) (D i))
set_option quotPrecheck false
local notation "X₀"=> enters V (S.ratio.parent o) (reach x) g D (a.extra g u Ω)
-- Probe kit before mean. L' ℝ caller. Both input-output orientations. No extensions used on tall Bore.
local notation "K"=> S.patch.L
local notation "Kₜ"=> (C.M + tranche S.patch.L n E.Q (loom P (reach x) C.C) (u*‖tape Ω‖) B.threshold)
include Z hp hg hz hk ho hV hu hv hl hD
variable (k q d)
include k q d U
variable (p':Kit.Rail f c)(hΦ: Warp S.patch.L o (S.ratio.parent o) p' N W w t m)(G: Crate c N→L[ℝ]ℝ)(hG:∀ X, ‖G X‖ ≤ Stew.plank (S.ratio.parent o) w X) (hP : Woven o X B W H τ){b:Bool}(h:Loan b H o)
include hΦ hG hP h
lemma quasar3 : let L:= X₀; let z:= display T F x k true ∘ L; let f:=(G.comp (bill p' N)) ∘ H ∘ increment 1 ; Through n (f ∘ z) 0 ((flareN Z τ (Jive m))*(fern K)^(furl b)*Kₜ ^n) :=by
    intro L z f; obtain ⟨hp',hj,hs,hv',hT⟩:= chordD k q d a hp hg hz hk ho hV U Ω hu hv hl hD
    obtain ⟨he,ha,hh,hF⟩:= priceLoan hP hΦ.flesh hΦ.height hΦ.ready hΦ.coin0 hΦ.pay h G hG
    have hx : ContDiffAt ℝ n f (z 0) := (Hera.along (x:=z 0) ha (show Healthy B.threshold X _ from by simpa only [one_smul] using hv' 1 (by simp))).of_le (by exact_mod_cast hp.rehearsed.orders)
    let u:= (Kₜ); have hη:1≤u:= le_trans C.matins (le_add_of_nonneg_right (tranche_nn _ _ (zero_le_one.trans E.majorant) (mul_nonneg hu (norm_nonneg _)) B.threshold_pos.le))
    have hZ:= Z.large
    refine ⟨hx.comp (f:=z) 0 hp',fun j hj' =>?_⟩
    refine (slots_bound (U:=z) hp' hx hj' (C:=(n+1:ℝ)*(3*((3*u)^n*(fern K)^(furl b)))*Z.fee*(Jive m*τ)) (by positivity [fern_pos K]) ?_).trans_eq ?_
    · intro p v hv; have hC := Hera.crystal3 (C:=u) ha (fern_pos K).le (fern_one K) hη Z hp.rehearsed.orders he hh (if b then 1 else 0) (by split <;> omega) hF (z 0) hj hs hv' (by omega) (p.length_le.trans hj') (fun i=>iteratedFDeriv ℝ (p.partSize i) z 0 (fun j=> v (p.emb i j))) (fun i=> hT _ (p.partSize_pos i) ((p.partSize_le i).trans hj') _ (fun k=>hv _))
      exact hC
    unfold flareN u; rw [mul_pow]; ring
local notation "M₀"=> C.M * loom P (reach x) C.C
lemma siren3 (hv₀: M₀≤1) :
   let q':= fun B:Grid f=>G (bill p' N (H (gauge (g ∘ S.ratio.parent) B))); let B y:= q' (a.received k T q d u (journey V l D y) U Ω)
   Through n B 0 ((flareN Z τ (Jive m))*(fern K)^(furl b)*Kₜ ^n + tender Z τ M₀*Kₜ^n):=by
    intro q' B₀; let L:= X₀; let z:=display T F x k true ∘ L; let v y:= H (increment 1 (z y)); let G' (y:Panels l):= G (bill p' N (v y));
    have he₀ : Through n G' 0 _:= quasar3 k q d Z a hp hg hz hk ho hV U Ω hu hv hl hD p' hΦ G hG hP h -- binder
    let A y:= wash o N W (v y); let Y(y:Panels l):= φ T F true (L y).1; let M:= grain n M₀; let q₀:=patterns n*((3*Kₜ)^n*Z.fee*τ)
    have hp' : Through n A 0 q₀:= inStep k q d Z a hp hg hz hk ho hV U Ω hu hv hl hD hP
    have hY : Through n Y 0 M₀:= taxes (F:=F) C hp hg (by omega) hD hl
    let U' y:= merchant (S.ratio.parent o) o p' w W hΦ.ready y N; let I (y:Panels l):= U' (pulseQ f (Y y))-U' (pulseQ f 0)
    have hI : Through n I 0 M:= staring Y 0 hY hv₀ (by omega) p' hΦ
    have hh := steadyX _ _ _ hp' hI
    let X:=Stew.bias (Stew.lens (N:=N) (S.ratio.parent o)) w; let V':Crate c N→L[ℂ]Crate c N:=(rave (S.ratio.parent o) N w hΦ.height).symm.toContinuousLinearMap
    have hz'(x:Crate c N):V' (X x)=x:= (rave (S.ratio.parent o) N w hΦ.height).symm_apply_apply x
    let Q:=G.comp (V'.restrictScalars ℝ); have hQ: ‖Q‖≤1:=by
       apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro x; obtain ⟨v,hv⟩:= (uplifts (o:=S.ratio.parent o) (N:=N) hΦ.height).2 x; change X v=x at hv; subst x; change ‖G (V' _)‖≤ _; rw [hz',one_mul]; exact hG _
    let v':=fun y=> Q (I y (A y)); have hQ': Through n v' 0 (tender Z τ M₀ * Kₜ^n):=by
       have he:= Heir.linear_through (f:=fun y=> I y (A y)) Q hh hQ; rw [one_mul] at he; apply he.mono; unfold tender M snow q₀; apply le_of_eq; rw [mul_pow (3:ℝ)]; ring
    have ht:=hp.rehearsed; have hv := (depicted (k:=k) (q:=q) (d:=d) a hp.bulletin ht.weft (hp.acts F k) hz hg ho C.C_one ht.tensions.allows U Ω ((a.extra_size g u hu Ω).trans (hv.trans ht.tensions.noise)) D)
    have hc:= Heir.sum_through he₀ hQ'
    have hE:B₀=ᶠ[𝓝 0] G'+v':= by
       filter_upwards [hv] with i hi; unfold B₀ q'; let P':=a.received k T q d u (journey V l D i) U Ω; let D':=gauge (g ∘ S.ratio.parent) P'
       let g' j:=su.lieExp (Y i j); have he:v i=H (gauge g' D'):= hP.room _ _ (agrees_mono hi (fun _ hx=> Finset.mem_union_left _ hx))
       have hM Z: U' Z (A i)= X (apple p' N (changeVars (tor Z) (v i).val)):= commerce Z hΦ.ready _
       have hh₀: U' (pulseQ f 0) (A i)= X (bill p' N (v i)):=by rw [hM,holy]; rfl
       have hh₁: U' (pulseQ f (Y i)) (A i)= X (bill p' N (H D')):=by rw [hM, he,show changeVars _ _=(H D').val from composer P' (g ∘ S.ratio.parent) (Y i) h.gauge]; rfl -- composer inputs check
       change G (bill p' N (H D'))= G' i+ v' i; unfold v' I; rw [_root_.sub_apply,map_sub,hh₀,hh₁]; change _= G (bill p' N (v i)) + (G (V' (X _))-G (V' (X _))); rw [hz',hz']; abel
    exact ⟨hc.smooth.congr_of_eventuallyEq hE,fun i hi=> (congr_arg (‖·‖) ((hE.iteratedFDeriv (𝕜:=ℝ) i).eq_of_nhds)).trans_le (hc.pay i hi)⟩
end YM.QCD.Dust
namespace YM.QCD.Dust
open Function Filter Set Lattice Wilson Pressure RG Precision Tree Next Next.SectorChange Next.Fluctuations Next.Foundations
    Exterior Bloch Bid Push.SectorMeasure MultiNext.SignedSource MultiNext.SignedSource.Banjo Planned.AtomRegular MeasureTheory Analysis
open AnalyticBridge.SectorAffine.Offset WardBin.Lies PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Lat Kit Grass Brick Cove Stew ConnectedActivityE6.Blaze Push.Uniform Patron Reggae AnalyticBridge.LocalGaussian.Moments AnalyticBridge.VerifiedReset
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {c f : Side} {S : StepData c f} {T : Tube su S} {Pt : Teller su} {k : S.Choices} {V : Config su c} {F : Forest S.ratio} {L:Side}
    {P B : BudgetPoint} {o : Site f} {g : Site c → su.El} {X : Support f} {Y : Support c} {Q M m r t x τ W w σ G₀ ρ v R : ℝ} {I : Type} {J: BudgetPoint}
    {A : Stores S} {n l N j : ℕ} {D : Slab su c l} {q : Chi} {d u : ℝ} {f' : Config su f → ℝ} {H:Grid f→EvenA f N}
-- Height lease. Test adapted to A.F.
variable {C: Libretto su n}{E: Record}
-- ensure C channel positive. `Leader` and bancada
variable (Z:Hera.Rights su n)(a:Museum F x A X Y I) [Fintype I]
    (hp:Plays C E P B Pt T x) (hg :Canvas P (S.ratio.parent o) (reach x) V g n C.C)
variable (hz:Short S B X)(hk:5≤n)(ho:o∈X)(hV: Healthy P.threshold Y V) (U:Config su f)(hu:0 ≤u)
variable (p':Kit.Rail f c)(hΦ: Warp S.patch.L o (S.ratio.parent o) p' N W w t m)(G: Crate c N→L[ℝ]ℝ)(hG:∀ X, ‖G X‖ ≤ Stew.plank (S.ratio.parent o) w X)
section canopy
variable (hP: Woven o X B W H τ) {b:Bool}(h:Loan b H o) (k q d) {Γ:Prices su I→ℝ}(hΓ:Silences su I n u (E.ε*B.threshold) Γ)
include Z hp hg hΦ hz hk ho hV hu hΓ hG hP h
set_option quotPrecheck false
local notation "s"=> C.M * loom P (reach x) C.C
local notation "K"=> S.patch.L
-- joint smooth for ANY purchased scalar. No invoice off-domain action. 
lemma ebony3 (ht : s≤1)(hy:tender Z 1 s ≤fern K^(furl b)) (j:ℕ): let V':= skimR (g∘ S.ratio.parent) G p' H; let Y' := flareN Z τ (Jive m)*(fern K)^(furl b) + τ*fern K^(furl b)
    Hera.Fugue a U V' T C E P B j Γ u Y' k q d o V:=by
   intro V' Y' ξ hξ; have h₁:=hΓ.stay ξ hξ
   let L:= C.M+tranche K n E.Q (loom P (reach x) C.C) (u*‖tape ξ‖) B.threshold; have hl:1 ≤ L:= le_trans C.matins (le_add_of_nonneg_right (tranche_nn _ _ (zero_le_one.trans E.majorant) (mul_nonneg hu (norm_nonneg _)) B.threshold_pos.le)) -- argument
   have hs : L ≤ _:=trough (E:=E) (C:=C) (P:=P) (B:=B) ξ u x hu c f S.patch.L X j
   have hJ(i)(hi:i≤n)(A: Slab su c i)(hA: ∀ j,P.dirBound (S.ratio.parent o) (A j)) := siren3 k q d Z a hp hg hz hk ho hV U ξ hu h₁ hi hA p' hΦ G hG hP h ht
   have he : tender Z τ s ≤ τ*(fern K)^(furl b):=by rw [show tender Z τ s=τ*tender Z 1 s from ?_]; exact mul_le_mul_of_nonneg_left hy hP.travel; unfold tender; ring
   have hh:0 ≤ Y':=by
      have hf := hJ 0 (Nat.zero_le _) 0 (fun j=>j.elim0); let P':=(flareN Z τ (Jive m)*(fern K)^(furl b)); have hρ:0≤ P'*L^n+tender Z τ s*L^n:= hf.nonneg
      have hp : tender Z τ s * L^n ≤ τ*(fern K)^(furl b) * L^n := mul_le_mul_of_nonneg_right he (pow_nonneg (zero_le_one.trans hl) _)
      change 0≤P'+τ*fern K^(furl b); exact nonneg_of_mul_nonneg_left (b:=L^n) (by rw [add_mul]; linarith only [hp,hρ]) (by positivity) -- ensure lemma expects ?
   constructor
   · let p := hp.rehearsed; obtain ⟨u',hr⟩:= framed a hV hp.space (by omega) (Z:=C.Z) p.wire
     have hW := border_healthy hp.sew C.width C.price p.early (hp.acts F k) E.majorant (by omega) p.tensions a hp.bulletin C.Z rfl p.wire hp.space p.temp_eq hV U ξ hu h₁ B.threshold_pos (q:=q) (d:=d)
     obtain ⟨hv,hx⟩:= a.joint_overt (d:=d) (q:=q) (w:=ξ) (u:=u) (hp.acts F k) hp.bulletin hr U C.C_one p.tensions.allows (fun g=> (a.extra_size g u hu ξ).trans (h₁.trans p.tensions.noise))
     let W (z : Directions su c × Prices su I) := a.overt T k V u ξ u' (increment V z.1) z.2
     have hW₁ : W (0,ξ)=0 := by unfold W; rw [Work.G07.at_zero_increment,a.overt_home]
     let P'' := g ∘ S.ratio.parent
     -- gauge gᵥ. rewrite using slots P''^-1
     let f:=orbitL (rotates N P''⁻¹)
     have hQ1:V'= (G.comp ((bill p' N).comp f)) ∘ H:=by
         funext U; let W:= H (gauge P'' U); have hx: gauge P''⁻¹ (gauge P'' U)=U:=by funext i; simp only [Lattice.gauge,Pi.inv_apply]; group
         have ht:sways (Lat.rotates N P''⁻¹) (H U)= W:=Subtype.ext (by rw [← hx]; exact h.gauge (gauge P'' U) _)
         exact congr_arg (G ∘ (bill p' N)) ht.symm
     have hK':Ease.Charm B X H:= ⟨hP.room,hP.use⟩; have hH : Ease.Charm B X V':=hQ1.symm ▸ (hK'.scales _)
     exact ((show ContDiffAt ℝ (↑n) (V' ∘ increment (a.received k T q d u V U ξ)) (W (0,ξ)) by rw [hW₁]; exact (hH.smooth _ hW).of_le (Nat.cast_le.mpr p.orders)).comp (f:=W) _ hv).congr_of_eventuallyEq (hx.mono (fun _ hz => hH.sites _ _ hz))
   intro l hl' A hA
   apply ((hJ l hl' A hA).pay l hl').trans; refine le_trans (b:=Y'*L^n) ?_ (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans hl) hs _) hh); unfold Y'; rw [add_mul]; exact add_le_add le_rfl (mul_le_mul_of_nonneg_right he (pow_nonneg (zero_le_one.trans hl) n))
end canopy
end YM.QCD.Dust
#print axioms YM.QCD.Dust.ebony3
