import YM.MassiveQCD.Relight.Wax
import YM.MassiveQCD.Festival.Park
import YM.QCD.Finch.Trust
/-! # Colored Charge interfaces for re-expression after mass accounting
 Must enter `Hill` Step at coarser tick, carrying genuine all-power budgets & reflection masks. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Relight
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Port Brick Dust Reggae Stem Stew Stew.Phased
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N n:ℕ} {a r u t σ η ξ T θ x:ℝ}{p:BudgetPoint}{o:Site c}
open Villa Revolve Flume Quarry AnalyticBridge.VerifiedReset Footprint Jets.Touch Kites
variable {I J K K₀:Type}
open Ruby Ruby.LanternK Acre Acre.Rails
open Festival
variable (X:Gem c N I)(Y:Ruby.Hue c N I)(v:I→ℕ)(s:ℕ→ℂ)
set_option quotPrecheck false
local notation "K*"=> v ∘ Prod.snd
lemma clean : weight (glean X) (K*) s=glean (weight X v s):=by
    unfold glean weight; congr 1; funext i U; simp only [Function.comp_apply,Pi.smul_apply]; rw [swayC,smul_comm] -- simp
lemma cleaner : bleach (Ruby.HGrace Y) (K*) s=Ruby.HGrace (bleach Y v s):=by unfold bleach HGrace; congr 1; funext i U; simp only [Function.comp_apply,Pi.smul_apply]; rw [swayC,smul_comm]
open Finch
lemma glimmer (he:Noted X): RotationE (glean X) (K*):=by
   refine ⟨noted _ he,fun r k g hh=>?_⟩
   refine ⟨Equiv.prodCongr (skyEquiv r) (Equiv.refl _),?_⟩; rintro ⟨p,i⟩; refine ⟨rfl, ?_,fun U=>?_⟩
   · change rotateL (X.addr i) (pod r p)=rotateL (rotateL (X.addr i) p) r; unfold rotateL; congr 1
     · exact Equiv.congr_fun (podA ..) _
     change (X.addr i).support.image _=((X.addr i).support.image _).image _; rw [podA,image_image]; rfl
   change Diode N r k g (averageC c • spice p (X.view i (Strut.sky p (Strut.sky r U))))= averageC c • spice (pod r p) (X.view i (Strut.sky (pod r p) U)); rw [skying,eSM _ (phare _)]; apply congr_arg; change sways _ (sways _ _)=_; rw [leaps,← copies_mul,← beset _ _ _ _ g (ink p)]; exact AccentFit.coinT (X.view i _) (he.num i _) (Strut.comb hh (assured p)) (assured _)

lemma hailed (ht:LampInk Y): Yank (Ruby.HGrace Y) (K*):=by
    have hf:= Ruby.track_average Y ht.gauge ht.fit ht.real; refine ⟨⟨hf.gauge,hf.real,hf.number⟩,fun s k g h=>?_⟩; refine ⟨Equiv.prodCongr (skyEquiv s) (Equiv.refl _),?_,fun _=> rfl,?_⟩
    · rintro ⟨p,i⟩; change (Y.bud i).image (act (pod s p))=((Y.bud i).image (act p)).image (act s); rw [podA,image_image]; rfl
    rintro ⟨p,i⟩ U; change Diode N s k g (averageC c • spice p (Y.mean i (sky p (sky s U))))= averageC c • spice (pod s p) (Y.mean i (sky (pod s p) U)); rw [skying,eSM _ (phare _)]; apply congr_arg; change sways _ (sways _ _)=_; rw [leaps,← copies_mul,← beset _ _ _ _ g (ink p)]; exact AccentFit.coinT (Y.mean i _) (ht.fit i _) (Strut.comb h (assured p)) (assured _)


lemma wax_grace (he:Wax Y p.threshold p.B σ T t)(h:fareG 1 r N≤t)(hz:0<r): Wax (HGrace Y) p.threshold p.B σ T r:=by
   obtain ⟨f,hp,hQ⟩:=he.expense; let N₀ i:= averageC c*f i
   refine ⟨Ruby.rak _ he.burns,N₀∘Prod.snd,?_ ,fun i V=>?_⟩
   · intro x;
     refine budget_rows _ _ (fun v=> ?_) (copiesG (c:=c) (budget_nonneg (hp 0))); convert! budget_scale (avPos c|>.le) (hp ((act v).symm x)) using 1; ext i
     let z:=(act v).symm x; have hx: x∈(HGrace Y).bud (v,i) ↔ z∈Y.bud i:=by nth_rw 1 [← (act v).apply_symm_apply x]; change act v z∈Finset.image (act v) (Y.bud i) ↔ _; simp
     rw [show coverNumber p.B ((HGrace Y).bud (v,i))=coverNumber p.B (Y.bud i) from cover_map (act v) (turn_sep _ _) ..]; by_cases h:x∈ (HGrace Y).bud (v,i)
     · rw [if_pos h, if_pos (hx.mp h)]; exact mul_assoc ..
     rw [if_neg h,if_neg (mt hx.mpr h),mul_zero]
   rcases i with ⟨v,i⟩; let A:= spice v (Y.mean i (Strut.sky v V)); change ‖token _ _ _ (averageC c • A)‖≤_
   have ht : token c N r (averageC c • A)=averageC c • token c N r A:=map_smul ((token c N r).restrictScalars ℝ) ..  -- wrong token vs songT defeq?
   rw [ht,norm_smul,Real.norm_of_nonneg (avPos _|>.le)]; exact mul_le_mul_of_nonneg_left (((soared v 0 t h hz _).2).trans (hQ _ _)) (avPos ..|>.le)

end YM.QCD.Relight
