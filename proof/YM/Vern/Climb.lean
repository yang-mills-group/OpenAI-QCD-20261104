import YM.Vern.Count
set_option maxHeartbeats 640000
set_option autoImplicit false
noncomputable section
namespace YM.Vern
open Function Set Filter Analysis MeasureTheory Lattice QCD QCD.Lat
open Massive Massive.UV Massive.Tarn Massive.Tarn.Choir Massive.Tarn.Choir.Strip Massive.Patria.Gall.Onyx
open Massive.Tarn.ChargeQ Massive.Poised.Plans.Stamp.Stair Massive.Gust
open scoped Topology ContDiff BigOperators Classical ComplexOrder Matrix InnerProductSpace
open Sprig Intag.Sprig UV.Free Massive.Poised.Plans.Stamp Heron Iceberg Lobo
open scoped YM.Iceberg
variable {C:Sequence}{P:Calibration C}{K:Choir}{T:Pollens P K}{d:ℕ}{ε β:ℝ}
variable {φ:ℕ→ℕ}(hp:C.Path β ε)(hQ:Tendsto φ atTop atTop)(hP:P.System)(hf:Foil P K T)(HQ:K.Harmony P φ)(E:Canopy P φ K)(X:Lanterns T E)
variable (V:Axis× Axis→ K.W)(hV: Persona T V)(J:Axle K (fun a b=>V (a,b))) (B:Vane J)
variable (r:ℝ)
local notation "F" => Axis× Axis
include hV
lemma valeS (r:ℂ):Tense T (r • V) :=by
      let H:= hV.tense; refine ⟨fun i=>(K.level 8).smul_mem r (H.lv i),fun a b=>congr_arg (r • ·) (H.sym ..),fun i=>?_,fun i=>?_,fun p i=>?_,fun p s h i j=>?_⟩ <;> simp only[Pi.smul_apply,map_smul,H.parity,H.charge,H.flux]; rw[H.geo p s h,smul_comm]
lemma paleS (h:r ≠0): Persona T ((r:ℂ) • V):=by
      refine ⟨valeS V hV (r:ℂ),?_,?_,?_⟩; · rw [map_smul,hV.div,smul_zero]
      · intro a; have he: roseC T a ((r:ℂ) • V)=(r:ℂ) • roseC T a V:=by
                      funext i; change _ • T.adj a ((r:ℂ) • _)= (r:ℂ) • _; rw[map_smulₛₗ, show starRingEnd ℂ (r:ℂ)=(r:ℂ) from Complex.conj_ofReal _]; exact smul_comm ..
        rw [he,hV.real'a]
      intro z hv; apply hV.non ((r:ℂ)⁻¹*z); rw [← smul_smul,←hv, inv_smul_smul₀ (by exact_mod_cast h)]
omit hV
noncomputable def ang (r:ℝ): Axle K (fun a b=> (((r:ℂ) • V) (a,b))) where
     jet := (r:ℂ) • J.jet
     landed d h g u ht:= (K.level d).smul_mem _ (J.landed d h g u ht)
     relation g u n x χ hx hw v:=by
           rw[Pi.smul_apply,LinearMap.smul_apply,map_smul,← J.relation g u n x χ hx hw v]
           unfold about fluxG; rw [smul_neg]; congr 1; rw[Finset.smul_sum]; refine Finset.sum_congr rfl fun a _=>?_ ; rw[Finset.smul_sum]; refine Finset.sum_congr rfl fun b _=>?_ ; rw[← integral_smul]; apply integral_congr_ae; refine Eventually.of_forall fun i=>?_ ; dsimp only; unfold termG; rw[← heads, ← heads]; change _ * (headG _ _ ((r:ℂ) • V (a,b)))= (r:ℂ) • _; rw[map_smul]; exact mul_smul_comm ..
include hV
lemma arc_cG(h:r≠0) (k:ℕ): paceG ((r:ℂ) • V) (paleS V hV r h).tense E X k=(r:ℂ) • paceG V hV.tense E X k:=by
      funext i; unfold paceG; simp only[Pi.smul_apply]; unfold airs; rw [show (liftV ((r:ℂ) • V) (paleS V hV r h).tense i)= (r:ℂ) • liftV V hV.tense i from rfl, map_smul]; exact smul_comm ..
lemma angl (g:Ortho.Skew)(k:ℕ)(h:8≤d)(x:Free.Symbol d): steel ((r:ℂ) • V) E X (ang V J r) h g k x=(r:ℂ) • steel V E X J h g k x:=by
     apply (X.frame k d).injective; apply Subtype.ext; unfold steel; simp only[LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,map_smul]; rfl
variable (hY: onceF K (V (0,0))=0)(hD:(swingE K 1).range=(bits K).range)(hχ:∀ d, ∃ n:Lattice.Side, Injective (P.candidate d n 0))
open Finset
structure Glacier (T:Pollens P K) (E:Canopy P φ K)(X:Lanterns T E)(W:Axis×Axis→K.W)(A: Axle K (fun a b=>W (a,b)))(f:ℕ→ℕ): Prop where
      n: Persona T W
      period: Tendsto f atTop atTop
      sea:Tendsto ((paceG W n.tense E X) ∘ f) atTop (𝓝 (Tawny.Cast.Drill.symbS 1 (bendP (fun _=>1))))
      angV:∀ d:ℕ,∀ h:8 ≤ d,∀ g:Ortho.Skew,∀ Δ:ℝ→EuPin,∀ hh:EuPin.Path g Δ,∀ u:Free.Symbol d,Tendsto (fun i=>steel W E X A h g (f i) u) atTop (𝓝 (reachΩ g Δ hh (fun _=>1) d u))
include hp hQ hP hf HQ X B hY hD hχ
open Tawny Tawny.Cast Tawny.Cast.Drill
lemma taxes:∃ (W:Axis×Axis→K.W)(A:Axle K (fun a b=>W (a,b)))(Fq:ℕ→ℕ), Glacier T E X W A Fq:=by
    obtain ⟨f,U,hs,hw,H⟩:= lives V E X hV -- signature? no k
    have hF:= hs.tendsto_atTop; obtain ⟨κ,R,hR,hκ,hpR⟩:= icon hp hP HQ hQ hf V E X hV f U H hF hY -- order
    have hA:Hail.RightAuth P.sym:= fun d v=>(Canopy.adornV T E hp hQ hP HQ hf v _).mp
    have hz(d:ℕ)(x:Free.Symbol d)(h:8≤d)(g:Ortho.Skew)(Δ:ℝ→EuPin)(ht:EuPin.Path g Δ):= mist HQ V E X hV J h g R f hF hpR Δ ht κ hκ hA x -- order
    have hE:∃ i:IceT,κ i≠0:=by
          by_contra! hh; have hp': U= 0:= by rw [← hR,hκ,bendP]; simp [hh]
          rw [hp',norm_zero] at hw; exact zero_ne_one hw
    obtain ⟨i,hi⟩:=hE; obtain ⟨r,hr,ht⟩:= blaze hf HQ E X V hV J B (show 8≤10 from by decide) f 0 (omegaQ 0 κ 10) hF (fun v=>hz 10 v _ _ _ (treks _)) (omega_non 0 P.sym hA κ i hi)
    have hM(d:ℕ)(x:Free.Symbol d)(hh:8 ≤ d)(g:Ortho.Skew)(Δ:ℝ→EuPin)(h:EuPin.Path g Δ): Tendsto (fun i=> steel V E X J hh g (f i) x) atTop (𝓝 ((r:ℂ) • reachΩ g Δ h κ d x)):= sees E X V hV J r g f (reachΩ _ _ _ _ _) hh ht hr x (hz _ _ hh g Δ h)
    have hσ:= grist hP hf HQ E X V hV J B r κ hD hχ f hF hA (fun d x hh k=>by
          have h:= tendsto_const_nhds (x:=(↑r⁻¹:ℂ))|>.smul (hM _ x hh (Omega k) (pathW k) (treks k)); rw [Complex.ofReal_inv, inv_smul_smul₀ (by exact_mod_cast hr.ne')] at h; exact_mod_cast h) -- type casts maybe push
    let u:=κ none; have hX(i:IceT):κ i=u:=by cases i; rfl; exact (hσ _).symm
    have hu:u≠0:= hX i ▸ hi; let s:= (r*u)⁻¹; have h0:s≠0:= inv_ne_zero (mul_ne_zero hr.ne' hu)
    let J':=ang V J s; refine ⟨(s:ℂ) • V,J',f, paleS V hV s h0,hF,?_,?_⟩
    · let D:= symbS 1 (bendP (fun _=>1)); have hv: U=(u:ℂ) • D:=by
           rw[←hR,hκ]; simp only[D,bendP,hX,_root_.map_sum,map_smul,Finset.smul_sum,one_smul]
      have ha:Tendsto (fun i=>paceG V hV.tense E X (f i)) atTop (𝓝 ((r:ℂ) • U)):=by
           apply (((Complex.continuous_ofReal.continuousAt.tendsto).comp ht).smul H).congr'; refine Eventually.of_forall fun i=>?_; change (↑(_:ℝ):ℂ) • aceG V E X (f i) hV.tense=_; unfold aceG; push_cast; rw[smul_inv_smul₀ (by exact_mod_cast (viable V E X (f i) hV).ne')]
      have hp:= (tendsto_const_nhds (x:=(s:ℂ))).smul ha; rw [hv,smul_smul, smul_smul,show (((s:ℂ)*↑r)*↑u)=1 from (by unfold s; rw [mul_assoc, ← Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_mul, ← Complex.ofReal_mul,inv_mul_cancel₀ (by exact_mod_cast mul_ne_zero hr.ne' hu)]),one_smul] at hp -- smul_smul rewrites LIFO
      exact hp.congr' (Eventually.of_forall fun i=> (arc_cG E X V hV s h0 (f i)).symm)
    intro d hh g Δ h x
    have hx: reachΩ g Δ h κ d x=(u:ℂ) • reachΩ g Δ h (fun _=>1) d x:=by unfold reachΩ; simp only [LinearMap.sum_apply,LinearMap.smul_apply,Finset.smul_sum,hX,Complex.ofReal_one,one_smul]
    have ht:= (tendsto_const_nhds (x:=(s:ℂ))).smul (hM d x hh g Δ h); rw [hx,smul_smul, smul_smul,show (((s:ℂ)*↑r)*↑u)=1 from (by unfold s; rw [mul_assoc, ← Complex.ofReal_mul, Complex.ofReal_inv, inv_mul_cancel₀ (by exact_mod_cast mul_ne_zero hr.ne' hu)]), one_smul] at ht; exact ht.congr' (Eventually.of_forall fun i=>(angl E X V hV J s g (f i) hh x).symm)
end YM.Vern
#print axioms YM.Vern.arc_cG
#print axioms YM.Vern.ang
#print axioms YM.Vern.taxes
