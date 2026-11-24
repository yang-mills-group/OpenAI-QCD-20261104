import YM.QCD.Dust.Melody
import YM.QCD.Reggae.Oc
/-! # Good conversion for the massless publishers. Exact feefor arity-nonwrap. -/
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
-- Height lease. Test adapted to A.F.
variable {C: Libretto su n}{E: Record}
-- ensure C channel positive. `Leader` and bancada
lemma trough (A:Prices su I)(u x:ℝ)(hu:0 ≤ u)(c:Side)(f:Side)(K:Side)(X:Support f)(r:ℕ)[Fintype I] :C.M+tranche K n E.Q (loom P (reach x) C.C) (u*‖tape A‖) B.threshold ≤ Heir.Lute.leading C+Lute.rust C E P B K X r x u*powers A^2 :=by
   let s:=powers A^2; have hs:1 ≤ s:=one_le_pow₀ (grows A); have hQ:= E.majorant
   let v := loom P (reach x) C.C; let b := Lute.rust C E P B K X r x u
   have ht: tranche K n E.Q v (u*‖tape A‖) B.threshold ≤ b*s:=by
      apply le_trans (b:=tranche K n E.Q v u B.threshold*s) ?_ (mul_le_mul_of_nonneg_right
        ((le_add_of_nonneg_left (Heir.segment_nn n X P B E.majorant C.matins)).trans (le_add_of_nonneg_right (Lute.scratch_nn n))) (sq_nonneg _))
      have H := le_mul_of_one_le_right (mul_nonneg ((by positivity : (0:ℝ) ≤ 2*E.Q).trans (clinicFee_le n (zero_le_one.trans E.majorant))) (sq_nonneg v)) hs
      have hh: ‖tape A‖ ≤ s := (Lute.tape_control A).2.trans (le_self_pow₀ (grows A) two_ne_zero)
      unfold tranche; calc
       _ ≤ (clinicFee n E.Q*v^2*s + u*s)/B.threshold*(K.val:ℝ)^3 := by have h := B.threshold_pos; gcongr
       _ = _ := by ring
   apply add_le_add _ ht; unfold Lute.leading; nlinarith [C.matins,C.C_one,Nat.cast_nonneg (α:=ℝ) n]
variable (Z:Hera.Rights su n)(a:Museum F x A X Y I) [Fintype I]
    (hp:Plays C E P B Pt T x) (hg :Canvas P (S.ratio.parent o) (reach x) V g n C.C)
variable (hz:Short S B X)(hk:5≤n)(ho:o∈X)(hV: Healthy P.threshold Y V) (U:Config su f)(hu:0 ≤u)
variable (p':Kit.Rail f c)(hΦ: Warp S.patch.L o (S.ratio.parent o) p' N W w t m)(G: Crate c N→L[ℝ]ℝ)(hG:∀ X, ‖G X‖ ≤ Stew.plank (S.ratio.parent o) w X)
-- currency unit transition tactile. wire spin.f body linear Fee.
def skimR (g:Frame f)(G: Crate c N→L[ℝ]ℝ)(p':Kit.Rail f c)(H:Grid f → EvenA f N)(V:Grid f): ℝ:=G (bill p' N (H (gauge g V)))
-- Biased purse cargo.
section canopy
variable (hP: Woven o X B W H τ) {b:Flavor N}(h:Sign H b o) (k q d) {Γ:Prices su I→ℝ}(hΓ:Silences su I n u (E.ε*B.threshold) Γ)
include Z hp hg hΦ hz hk ho hV hu hΓ hG hP h
set_option quotPrecheck false
local notation "s"=> C.M * loom P (reach x) C.C
local notation "K"=> S.patch.L
-- joint smooth for ANY purchased scalar. No invoice off-domain action. 
lemma ebony (ht : s≤1)(hy:tender Z 1 s ≤fern K^5) (j:ℕ): let V':= skimR (g∘ S.ratio.parent) G p' H; let Y' := flareN Z τ (Jive m)*(fern K)^5 + τ*fern K^5
    Hera.Fugue a U V' T C E P B j Γ u Y' k q d o V:=by
   intro V' Y' ξ hξ; have h₁:=hΓ.stay ξ hξ
   let L:= C.M+tranche K n E.Q (loom P (reach x) C.C) (u*‖tape ξ‖) B.threshold; have hl:1 ≤ L:= le_trans C.matins (le_add_of_nonneg_right (tranche_nn _ _ (zero_le_one.trans E.majorant) (mul_nonneg hu (norm_nonneg _)) B.threshold_pos.le)) -- argument
   have hs : L ≤ _:=trough (E:=E) (C:=C) (P:=P) (B:=B) ξ u x hu c f S.patch.L X j
   have hJ(i)(hi:i≤n)(A: Slab su c i)(hA: ∀ j,P.dirBound (S.ratio.parent o) (A j)) := siren k q d Z a hp hg hz hk ho hV U ξ hu h₁ hi hA p' hΦ G hG hP h ht
   have he : tender Z τ s ≤ τ*(fern K)^5:=by rw [show tender Z τ s=τ*tender Z 1 s from ?_]; exact mul_le_mul_of_nonneg_left hy hP.travel; unfold tender; ring
   have hh:0 ≤ Y':=by
      have hf := hJ 0 (Nat.zero_le _) 0 (fun j=>j.elim0); let P':=(flareN Z τ (Jive m)*(fern K)^5); have hρ:0≤ P'*L^n+tender Z τ s*L^n:= hf.nonneg
      have hp : tender Z τ s * L^n ≤ τ*(fern K)^5 * L^n := mul_le_mul_of_nonneg_right he (pow_nonneg (zero_le_one.trans hl) _)
      change 0≤P'+τ*fern K^5; exact nonneg_of_mul_nonneg_left (b:=L^n) (by rw [add_mul]; linarith only [hp,hρ]) (by positivity) -- ensure lemma expects ?
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
