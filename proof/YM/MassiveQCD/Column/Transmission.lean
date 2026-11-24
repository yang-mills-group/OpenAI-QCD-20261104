import YM.MassiveQCD.Column.Spin
import YM.MassiveQCD.Column.Corner
import YM.QCD.Dust.June

/-!
# Pointed spin + gauge

All payments on the Museum sector with weighted costs. We can enhance a column in these bills and still meet the same exact plays. Fields use the true k & χ data under hΓ. This is the Lin step *profile* estimate with deterministic f & test directions; last use at a principal merged-singleton instance will require the authentic grocery-gas caps & News too. See `Temper.flowers`. Structure includes five-reality but NO unmarked flavor degeneracy.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Dust
open Function Filter Set Lattice Wilson Pressure RG Precision Tree Next Next.SectorChange Next.Fluctuations Next.Foundations
    Exterior Bloch Bid Push.SectorMeasure MultiNext.SignedSource MultiNext.SignedSource.Banjo Planned.AtomRegular MeasureTheory Analysis
open AnalyticBridge.SectorAffine.Offset WardBin.Lies PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Lat Kit Grass Brick Cove Stew ConnectedActivityE6.Blaze Push.Uniform Patron Reggae AnalyticBridge.LocalGaussian.Moments AnalyticBridge.VerifiedReset
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {c f : Side} {S : StepData c f} {T : Tube su S} {Pt : Teller su} {k : S.Choices} {V : Config su c} {F : Forest S.ratio} {L:Side}
    {P B : BudgetPoint} {o : Site f} {g : Site c → su.El} {X : Support f} {Y : Support c} {Q M m r t x τ W w σ G₀ ρ v R : ℝ} {I : Type} {J: BudgetPoint}
    {A : Stores S} {n l N j : ℕ} {D : Slab su c l} {q : Chi} {d u : ℝ} {f' : Config su f → ℝ} {H:Grid f→EvenA f N}
variable {C: Libretto su n}{E: Record}
section soothe
variable (Z:Hera.Rights su n)(a:Museum F x A X Y I) [Fintype I] 
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
variable (p':Kit.Rail f c)(hΦ: Warp S.patch.L o (S.ratio.parent o) p' N W w t m)(G: Crate c N→L[ℝ]ℝ)(hG:∀ X, ‖G X‖ ≤ Stew.plank (S.ratio.parent o) w X) (hP : Woven o X B W H τ){gain:Bool}(h:Rebate o H gain)
include hΦ hG hP h
lemma Rebate.quasar : let L:= X₀; let z:= display T F x k true ∘ L; let f:=(G.comp (bill p' N)) ∘ H ∘ increment 1 ; Through n (f ∘ z) 0 ((flareN Z (τ * rampFee gain K) (Jive m))*(fern K)^5*Kₜ ^n) :=by
    intro L z f; obtain ⟨hp',hj,hs,hv',hT⟩:= chordD k q d a hp hg hz hk ho hV U Ω hu hv hl hD
    obtain ⟨he,ha,hh,hF,hM⟩:= h.pay Z hP hΦ.flesh hΦ.height hΦ.ready hΦ.coin0 hΦ.pay G hG (by omega)
    have hx : ContDiffAt ℝ n f (z 0) := (Hera.along (x:=z 0) ha (show Healthy B.threshold X _ from by simpa only [one_smul] using hv' 1 (by simp))).of_le (by exact_mod_cast hp.rehearsed.orders)
    let u:= (Kₜ); have hη:1≤u:= le_trans C.matins (le_add_of_nonneg_right (tranche_nn _ _ (zero_le_one.trans E.majorant) (mul_nonneg hu (norm_nonneg _)) B.threshold_pos.le))
    have hZ:= Z.large
    refine ⟨hx.comp (f:=z) 0 hp',fun j hj' =>?_⟩
    refine (slots_bound (U:=z) hp' hx hj' (C:=(n+1:ℝ)*(3*((3*u)^n*(fern K)^5))*Z.fee*(Jive m*(τ*rampFee gain K))) (by positivity [fern_pos K]) ?_).trans_eq ?_
    · intro p v hv; have hC := Hera.crystal (C:=u) ha (fern_pos K).le (fern_one K) hη Z hp.rehearsed.orders he hh hF hM (z 0) hj hs hv' (by omega) (p.length_le.trans hj') (fun i=>iteratedFDeriv ℝ (p.partSize i) z 0 (fun j=> v (p.emb i j))) (fun i=> hT _ (p.partSize_pos i) ((p.partSize_le i).trans hj') _ (fun k=>hv _))
      exact hC
    unfold flareN u; rw [mul_pow]; ring
local notation "M₀"=> C.M * loom P (reach x) C.C
lemma Rebate.siren (hv₀: M₀≤1) :
   let q':= fun B:Grid f=>G (bill p' N (H (Lattice.gauge (g ∘ S.ratio.parent) B))); let B y:= q' (a.received k T q d u (journey V l D y) U Ω)
   Through n B 0 ((flareN Z (τ * rampFee gain K) (Jive m))*(fern K)^5*Kₜ ^n + tender Z τ M₀*Kₜ^n):=by
    intro q' B₀; let L:= X₀; let z:=display T F x k true ∘ L; let v y:= H (increment 1 (z y)); let G' (y:Panels l):= G (bill p' N (v y));
    have he₀ : Through n G' 0 _:= Rebate.quasar k q d Z a hp hg hz hk ho hV U Ω hu hv hl hD p' hΦ G hG hP h -- binder
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
       filter_upwards [hv] with i hi; unfold B₀ q'; let P':=a.received k T q d u (journey V l D i) U Ω; let D':=Lattice.gauge (g ∘ S.ratio.parent) P'
       let g' j:=su.lieExp (Y i j); have he:v i=H (Lattice.gauge g' D'):= hP.room _ _ (agrees_mono hi (fun _ hx=> Finset.mem_union_left _ hx))
       have hM Z: U' Z (A i)= X (apple p' N (changeVars (tor Z) (v i).val)):= commerce Z hΦ.ready _
       have hh₀: U' (pulseQ f 0) (A i)= X (bill p' N (v i)):=by rw [hM,holy]; rfl
       have hh₁: U' (pulseQ f (Y i)) (A i)= X (bill p' N (H D')):=by rw [hM, he,show changeVars _ _=(H D').val from composer P' (g ∘ S.ratio.parent) (Y i) h.gauge]; rfl -- composer inputs check
       change G (bill p' N (H D'))= G' i+ v' i; unfold v' I; rw [_root_.sub_apply,map_sub,hh₀,hh₁]; change _= G (bill p' N (v i)) + (G (V' (X _))-G (V' (X _))); rw [hz',hz']; abel
    exact ⟨hc.smooth.congr_of_eventuallyEq hE,fun i hi=> (congr_arg (‖·‖) ((hE.iteratedFDeriv (𝕜:=ℝ) i).eq_of_nhds)).trans_le (hc.pay i hi)⟩
end soothe
section snapshots
variable (Z:Hera.Rights su n)(a:Museum F x A X Y I) [Fintype I]
    (hp:Plays C E P B Pt T x) (hg :Canvas P (S.ratio.parent o) (reach x) V g n C.C)
variable (hz:Short S B X)(hk:5≤n)(ho:o∈X)(hV: Healthy P.threshold Y V) (U:Config su f)(hu:0 ≤u)
variable (p':Kit.Rail f c)(hΦ: Warp S.patch.L o (S.ratio.parent o) p' N W w t m)(G: Crate c N→L[ℝ]ℝ)(hG:∀ X, ‖G X‖ ≤ Stew.plank (S.ratio.parent o) w X)
-- currency unit transition tactile. wire spin.f body linear Fee.
-- Biased purse cargo.
section canopy
variable (hP: Woven o X B W H τ) {gain:Bool}(h:Rebate o H gain) (k q d) {Γ:Prices su I→ℝ}(hΓ:Silences su I n u (E.ε*B.threshold) Γ)
include Z hp hg hΦ hz hk ho hV hu hΓ hG hP h
set_option quotPrecheck false
local notation "s"=> C.M * loom P (reach x) C.C
local notation "K"=> S.patch.L
-- joint smooth for ANY purchased scalar. No invoice off-domain action. 
lemma Rebate.ebony (ht : s≤1)(hy:tender Z 1 s ≤fern K^5) (j:ℕ): let V':= skimR (g∘ S.ratio.parent) G p' H; let Y' := flareN Z (τ*rampFee gain K) (Jive m)*(fern K)^5 + τ*fern K^5
    Hera.Fugue a U V' T C E P B j Γ u Y' k q d o V:=by
   intro V' Y' ξ hξ; have h₁:=hΓ.stay ξ hξ
   let L:= C.M+tranche K n E.Q (loom P (reach x) C.C) (u*‖tape ξ‖) B.threshold; have hl:1 ≤ L:= le_trans C.matins (le_add_of_nonneg_right (tranche_nn _ _ (zero_le_one.trans E.majorant) (mul_nonneg hu (norm_nonneg _)) B.threshold_pos.le)) -- argument
   have hs : L ≤ _:=trough (E:=E) (C:=C) (P:=P) (B:=B) ξ u x hu c f S.patch.L X j
   have hJ(i)(hi:i≤n)(A: Slab su c i)(hA: ∀ j,P.dirBound (S.ratio.parent o) (A j)) := Rebate.siren k q d Z a hp hg hz hk ho hV U ξ hu h₁ hi hA p' hΦ G hG hP h ht
   have he : tender Z τ s ≤ τ*(fern K)^5:=by rw [show tender Z τ s=τ*tender Z 1 s from ?_]; exact mul_le_mul_of_nonneg_left hy hP.travel; unfold tender; ring
   have hh:0 ≤ Y':=by
      have hf := hJ 0 (Nat.zero_le _) 0 (fun j=>j.elim0); let P':=(flareN Z (τ*rampFee gain K) (Jive m)*(fern K)^5); have hρ:0≤ P'*L^n+tender Z τ s*L^n:= hf.nonneg
      have hp : tender Z τ s * L^n ≤ τ*(fern K)^5 * L^n := mul_le_mul_of_nonneg_right he (pow_nonneg (zero_le_one.trans hl) _)
      change 0≤P'+τ*fern K^5; exact nonneg_of_mul_nonneg_left (b:=L^n) (by rw [add_mul]; linarith only [hp,hρ]) (by positivity) -- ensure lemma expects ?
   constructor
   · let p := hp.rehearsed; obtain ⟨u',hr⟩:= framed a hV hp.space (by omega) (Z:=C.Z) p.wire
     have hW := border_healthy hp.sew C.width C.price p.early (hp.acts F k) E.majorant (by omega) p.tensions a hp.bulletin C.Z rfl p.wire hp.space p.temp_eq hV U ξ hu h₁ B.threshold_pos (q:=q) (d:=d)
     obtain ⟨hv,hx⟩:= a.joint_overt (d:=d) (q:=q) (w:=ξ) (u:=u) (hp.acts F k) hp.bulletin hr U C.C_one p.tensions.allows (fun g=> (a.extra_size g u hu ξ).trans (h₁.trans p.tensions.noise))
     let W (z : Directions su c × Prices su I) := a.overt T k V u ξ u' (increment V z.1) z.2
     have hW₁ : W (0,ξ)=0 := by unfold W; rw [Work.G07.at_zero_increment,a.overt_home]
     let P'' := g ∘ S.ratio.parent
     -- Lattice.gauge gᵥ. rewrite using slots P''^-1
     let f:=orbitL (rotates N P''⁻¹)
     have hQ1:V'= (G.comp ((bill p' N).comp f)) ∘ H:=by
         funext U; let W:= H (Lattice.gauge P'' U); have hx: Lattice.gauge P''⁻¹ (Lattice.gauge P'' U)=U:=by funext i; simp only [Lattice.gauge,Pi.inv_apply]; group
         have ht:sways (Lat.rotates N P''⁻¹) (H U)= W:=Subtype.ext (by rw [← hx]; exact h.gauge (Lattice.gauge P'' U) _)
         exact congr_arg (G ∘ (bill p' N)) ht.symm
     have hK':Ease.Charm B X H:= ⟨hP.room,hP.use⟩; have hH : Ease.Charm B X V':=hQ1.symm ▸ (hK'.scales _)
     exact ((show ContDiffAt ℝ (↑n) (V' ∘ increment (a.received k T q d u V U ξ)) (W (0,ξ)) by rw [hW₁]; exact (hH.smooth _ hW).of_le (Nat.cast_le.mpr p.orders)).comp (f:=W) _ hv).congr_of_eventuallyEq (hx.mono (fun _ hz => hH.sites _ _ hz))
   intro l hl' A hA
   apply ((hJ l hl' A hA).pay l hl').trans; refine le_trans (b:=Y'*L^n) ?_ (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans hl) hs _) hh); unfold Y'; rw [add_mul]; exact add_le_add le_rfl (mul_le_mul_of_nonneg_right he (pow_nonneg (zero_le_one.trans hl) n))
end canopy
end snapshots
section ending
structure Temper (B:BudgetPoint)(X:Support f)(o:Site f)(gain:Bool)(H:Grid f→EvenA f N)(W τ:ℝ) : Prop where
 wine : Woven o X B W H τ
 view : shadeG H
 joy x: Regal f N (H x)=H x
 rack : gain → VanishAt o (octave (H 1))
 base :PointedSeed B o X ((Reggae.river f N) ∘ H)
lemma Temper.flour {gain:Bool} (h:Temper B X o gain H W τ)(hp:0 ≤ W): let y (v: Grid f):= octave (H v); Woven o X B W y (2*τ) ∧ Rebate o y gain:=by
    intro y; obtain ⟨h1,h2⟩:= spores o X _ h.wine h.view hp; have he := h.wine.addition ((wealthy N _ _ _ h1 h2 hp).byScalar (-1)); rw [norm_neg,norm_one,one_mul,neg_one_smul,←two_mul] at he
    have hc:y=H + (- (fun x=>ocean f N (Reggae.river f N (H x)))):=by funext x; exact sub_eq_add_neg ..
    refine ⟨hc.symm ▸ he,?_,h.rack,?_⟩
    · intro i; exact chooseP _ (h.joy i)
    · intro i U; let p:= H (Lattice.gauge U i); suffices a : sways (rotates N U) (octave p)= y i from congr_arg Subtype.val a
      have hg: sways (rotates N U) p=H i:=Subtype.ext (h.view ..); rw [octave,map_sub,hg, Reggae.thorough ..]; change _= octave (H i); rw [octave,← hg, mur]
variable (Z:Hera.Rights su n)(a:Museum F x A X Y I) [Fintype I]
    (hp:Plays C E P B Pt T x) (hg :Canvas P (S.ratio.parent o) (reach x) V g n C.C)
variable (hz:Short S B X)(hk:5≤n)(ho:o∈X)(hV: Healthy P.threshold Y V) (U:Config su f)(hu:0 ≤u)
variable (p':Kit.Rail f c)(hΦ: Warp S.patch.L o (S.ratio.parent o) p' N W w t m)(G: Crate c N→L[ℝ]ℝ)(hG:∀ X, ‖G X‖ ≤ Stew.plank (S.ratio.parent o) w X)
variable {gain:Bool}(h:Temper B X o gain H W τ)(k q d) {Γ:Prices su I→ℝ}(hΓ:Silences su I n u (E.ε*B.threshold) Γ)
include hΦ hG Z hp hg hz hk ho hV hu hΓ h
local notation "θ₁"=> C.M * loom P (reach x) C.C
local notation "L₀"=>S.patch.L
set_option maxHeartbeats 380000 in
lemma Temper.flowers (ht : θ₁ ≤1)(hy:tender Z 1 θ₁ ≤fern L₀^5) (j:ℕ): let Y' := (carryFee C Z m)*(τ* rampFee gain L₀) *fern L₀^5
    Hera.Fugue a U (skimR (g∘ S.ratio.parent) G p' H) T C E P B j Γ u Y' k q d o V:=by
   intro y; obtain ⟨hX,hΘ⟩:= Temper.flour h hΦ.ready.le; let p:=g ∘ S.ratio.parent; let M (x):=octave (H x)
   have hP:=Rebate.ebony k q d Z a hp hg hz hk ho hV U hu p' hΦ G hG hX hΘ hΓ ht hy j
   let v(x):=Reggae.river f N (H x); let L : ℝ→L[ℝ]ℝ:= G.comp ((bill p' N).comp (ocean f N)); let Y:= skimR p G p' M; let X₀:=skimR p G p' H
   have hh' r: ‖L r‖ ≤ ‖r‖:=by
       change ‖G (bill p' N (ocean f N r))‖≤_
       apply (hG _).trans; change Stew.plank (S.ratio.parent o) w (apple p' N (ocean f N r).val) ≤ _; exact (hΦ.along (ocean f N r).val).trans_eq (vintage o r _ hΦ.way.le)
   have hL : ‖L‖ ≤1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x=> (hh' _).trans (by rw [one_mul]))
   have he(z): X₀ z = Y z + L (v z):=by
       have hv:v (Lattice.gauge p z)=v z:= (h.base.good.symmetry _ _) -- gaugeInvariant 
       unfold X₀ Y skimR; rw [show H (Lattice.gauge p z)= M (Lattice.gauge p z)+ocean f N (v z) from Eq.symm (by rw [← hv]; exact sub_add_cancel ..)]; rw [map_add,map_add]; rfl
   intro z hz'; let u':= u; obtain ⟨h1,h2⟩:= hP z hz'; obtain ⟨h3,h4⟩:= (PointedSeed.fugue k q d h.base YM.QCD.simple a hp hk hV (spores _ _ _ h.wine h.view hΦ.ready.le).2 hu hz hΓ U j) z hz' 
   refine ⟨?_,fun i hi D hD=>?_⟩
   · let f' (y: Directions su c × Prices su I):=a.received k T q d u (increment V y.1) U y.2
     change ContDiffAt ℝ (↑n) (fun y=> X₀ (f' y)) (0,z); rw [show (fun y=> X₀ (f' y))=(Y ∘ f')+(L ∘ (v ∘ f')) from funext fun i=>he _]
     have hh : ContDiffAt ℝ (↑n) (Y ∘ f') (0,z):=h1; exact hh.add (L.contDiff.contDiffAt.comp (f:=v ∘ f') (0,z) h3)
   let P₀ (x:Panels i):= a.received k T q d u (journey V i D x) U z
   let g(w):= X₀ (P₀ w); let v':= (v ∘ P₀)
   -- need smooth from h1,h3 with journey and point. via Germ.prod etc
   have ht (g:Grid f→ℝ)(he:ContDiffAt ℝ n (fun y : Directions su c × Prices su I=> g (a.received k T q d u (increment V y.1) U y.2)) (0,z)): ContDiffAt ℝ i (g∘P₀) 0 :=by
       let Q(x):=g (a.received k T q d u x U z); have hR:Germ n Q V:= he.comp (f:=fun i=> (i,z)) 0 (contDiffAt_id.prodMk contDiffAt_const)
       exact Germ.journeys D (hR.prod hi) -- inspect names
   have hy': v'=fun x=> Reggae.river f N (H (P₀ x)):=rfl
   change ‖iteratedFDeriv ℝ i g 0‖ ≤ _; rw [show g=(Y ∘ P₀)+(L ∘ v') from (funext fun x=> he _), iteratedFDeriv_add_apply (ht Y h1) (L.contDiff.contDiffAt.comp 0 (ht v h3))]
   have hd := (L.norm_iteratedFDeriv_comp_left (ht v h3) (n:=i) le_rfl).trans ((mul_le_of_le_one_left (norm_nonneg _) hL).trans (h4 i hi D hD))
   apply (norm_add_le ..).trans; apply (add_le_add (h2 i hi D hD) hd).trans

   let m₁:= τ*rampFee gain L₀; let f0:=fern L₀; have hf : 0 < f0:=fern_pos _
   let w:= (Lute.leading C+Lute.rust C E P B L₀ X j x u*powers z^2)^n
   have hw:0 ≤ w:=pow_nonneg (by have hp:= Lute.rust_nn (C:=C) (D:=E) (P:=P) (B:=B) (X:=X) (r:=j) (x:=x) (L:=L₀) hu; positivity [Lute.leading_one C]) _
   have ht:= rampFee_gate L₀ gain
   have hτ:=h.wine.travel; let V₁:=rampFee gain L₀
   have hA:2*τ ≤ 2*m₁:=mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hτ (ht.1.trans ht.2)) (by norm_num :0≤(2:ℝ))
   let p:= Lute.phrase C; have hq:0≤p:=Lute.phrase_nn C; have hX:τ*p*f0^4 ≤ m₁*p*f0^5:=by
       have hv : (0:ℝ) < (S.patch.L.val:ℝ):=by positivity -- edit type
       calc
         _ = τ * (S.patch.L.val:ℝ)*p*f0^5 :=by unfold f0 fern; field_simp
         _ ≤ _ := by unfold m₁; gcongr; exact ht.2
   change (flareN Z (2*τ*V₁) (Jive m)*f0^5+_)*w + τ*p*f0^4*w ≤ y*w
   apply (add_le_add (mul_le_mul_of_nonneg_right (add_le_add_right (mul_le_mul_of_nonneg_right hA (pow_nonneg hf.le 5)) (flareN Z (2*τ*V₁) (Jive m)*f0^5)) hw) (mul_le_mul_of_nonneg_right hX hw)).trans_eq; unfold y carryFee flareN m₁ f0 V₁ p; ring
end ending
end YM.QCD.Dust
