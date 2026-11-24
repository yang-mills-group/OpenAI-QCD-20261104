import YM.Patria.Services
/-! Step-focused exact Calibration solutions on this run. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria
open Set Filter Function Finset Lattice Source
open scoped ContDiff Topology BigOperators Classical
namespace Depth
open QCD QCD.Lat UV Cylinder RG Wilson Grass MeasureTheory
variable {S:Scheme}{r:Side}{N d i m M:ℕ}
variable (A:Run S N r 6)(H:SourceRead.TaperHol) (sym:RawSym)
abbrev Bore (d:ℕ) := (c: Side) → Cover → Label d→ₗ[ℂ] Insertion c 6
variable (B: Bore d)
-- Orient B up and down.
structure Rubric : Prop where
   stone (c:Side)(b:Cover) : B c b (sym.unit d)=1
   advances (c:Side)(x: Label d)(b p:Cover): march p (B c b x)= B c (b+p) x
   parity (c:Side)(x:Label d)(b:Cover):Action.parity (B c b x)= B c b (sym.parity _ x)
   flavor(c:Side)(x:Label d)(b:Cover)(u): Action.flavor u (B c b x)= B c b (sym.flavor _ u x)
   charge(c:Side)(x:Label d)(b:Cover):Action.charge (B c b x)= B c b (sym.charge _ x)
   pin(c:Side)(x:Label d)(b:Cover)(s:Signed)(p:EuPin)(h:p.Lifts s): Action.pin p s (B c b x)= B c (s.act b) (sym.pin _ p x)
   eye(c:Side)(x:Label d)(b:Cover)(a:Axis): Action.adj a (B c b x)= B c ((Signed.mirror a).act b) (sym.adj _ a x)
variable (hf:Rubric sym B)
variable (u:Averaging)(b:Cover) (hA:A.Actual)
open Poised Plans Display
local notation "Sn" =>A.regulator.density
local notation "Q" => ratioTo S N i
local notation "cn"=> S.side r N
local notation "bn"=> B (S.side r N)
variable (X Y: Label d)
abbrev draft (S:Scheme)(r:Side)(B: Bore d) (N i:ℕ)(u:Averaging)(x:Label d):=visitor S N i (r:=r) u 0 (fun c=> B (S.side r N) c x)
abbrev setS (i:ℕ)(u:Averaging) (x:Label d) : Insertion (S.side r i) 6:=AllAt A i (A.regulator.density*draft S r B N i u x)
local notation "X'"=>draft S r B N i u
local notation "ξ"=>setS A B i u
-- additive
open Rolls
lemma draft_plus (i:ℕ): setS A B i u (X+Y)= setS A B i u X+ setS A B i u Y:=by
    unfold setS; rw [show draft S r B N i u (X+Y)=_ from ?_, mul_add,map_add]
    unfold draft visitor; simp_rw [roles,map_add]; exact congr_fun (training (k:=1) (M:=ratioTo S N i) (menu u) (fun b=> bn b X) (fun b=> bn b Y)) _ -- argument computed scanner
lemma draft_state (t:ℂ)(i:ℕ) : setS A B i u (t • X)= t • setS A B i u X:=by
    let L:= (t • (LinearMap.id (R:=ℂ) (M:=Insertion cn 6))).restrictScalars ℝ
    have h(p:Cover):bn p (t • X)= L (bn p X):= map_smul (bn p) ..
    unfold setS; rw [show draft S r B N i u (t • X)=t • draft S r B N i u X from ?_, mul_smul_comm,map_smul]; unfold draft visitor; simp_rw [h,roles]; exact Eq.symm (rollLinear (l:=menu u) (M:=ratioTo S N i) (k:=1) (fun i=> bn i X) _ L) -- argument order
noncomputable def helm (A:Run S N r 6)(B:Bore d)(u:Averaging)(i:ℕ):Label d→ₗ[ℂ]Insertion (S.side r i) 6:={toFun:=setS A B i u,map_add':=fun x y=>draft_plus A B u x y i,map_smul':=fun v x=>draft_state A B u x v i}
local notation "Wt"=>helm A B u
-- problem data.
structure Wager (W:Market S r d)(i:ℕ): Prop where
   siteM : i ≤ N
   living: 18 ≤(S.side r i).val
   journey : Pilgrimage A H (fun b x=>B (S.side r N) b x) W i
   reading (x: Label d) : Beacon.ActionTest H 0 (B (S.side r i) 0 x) x.val
-- Lighted form
variable (W:Market S r d)(hW:Wager A H B W i)
abbrev Fuel (i:ℕ) (u:Averaging)(x y:Label d):= Tally H 0 y (A.density i) (setS A B i u x)
local notation "F"=> Fuel A H B
include hW hA
lemma arises_nonzero (q:Bool)(hX: X ≠0) (hp:moored X.val q): ∃ y:Label d,y≠0∧ Fuel A H B i u X y:=by
   obtain ⟨y,hF,hP⟩:= abundance A H (fun b x=>B cn b x) u hA W hW.journey X hp hX hW.siteM le_rfl; exact ⟨y,hF,hW.journey.furnished 0 _ _ _ le_rfl hW.siteM _ (hP 0)⟩
include hf
-- get unit then zero irrespective horizon
lemma bequeath : F i u (sym.unit d) (sym.unit d) :=by
    have h: draft S r B N i u (sym.unit d)=1:=by
        let P:=Q; have hQ:0<P:=Odd.pos (odd_to hW.siteM); unfold draft visitor; simp_rw [hf.stone, roles]; let X:=Insertion cn 6; change rolls 1 P _ (fun _=> (1:X)) _ = 1
        suffices h : ∀ x: List PairS, rolls 1 P x (fun _=> (1:X))=(fun _=>1) by rw [h]
        intro x; induction x with| nil=>rfl|cons c l ih=> rw [rolls,ih]; funext x; rw [sumG]; simp only [Finset.sum_const,card_univ,Fintype.card_fin,← Nat.cast_smul_eq_nsmul ℝ,smul_smul, inv_mul_cancel₀ ((Nat.cast_pos.mpr hQ):(0:ℝ)<P).ne',one_smul]
    unfold Fuel setS; rw [h,mul_one,← show (A.density i)=(AllAt A i Sn) from pier A hA hW.siteM]
    -- obtain IsUnit via any nonzero moored form, e.g. sym.unit
    let u0:=sym.unit d; have hm(u:Label d): sym.parity _ u= u→ moored u.val false:=fun h=>by unfold moored; rw [← sym.parityActs,h]; exact (one_smul ℂ u.val).symm
    have hne:u0 ≠0:=by intro h; have hp:= hf.stone cn 0; change bn 0 u0=1 at hp; rw [h, map_zero] at hp; have ht := DFunLike.congr_fun hp (1:Grid cn); exact zero_ne_one ht
    have hPS : moored u0.val false:=by apply hm; apply Subtype.ext; rw [sym.parityActs, show (u0).val = _ from sym.unitActs d]; unfold parityAct UV.unit; rw [TensorProduct.map_tmul]; simp
    obtain ⟨p,hp,hq⟩:= arises_nonzero A H B u hA u0 W hW false hne hPS -- includes hf? defined before
    have hh:= hW.reading u0; let R:= Patria.Canvas.foil (A.density i) (A.density i); let v:= (S.side r i); let p:= ⇑(B v 0 u0)
    refine ⟨hq.unit,fun J=>?_⟩; have he: Beacon.moment (d:=d) H 0 J R =ᶠ[𝓝 0] Beacon.moment H 0 J p:=by
       filter_upwards [(centered H 0 J (c:=v) (d:=d)).eventually hq.unit] with u hu; change adapter _ _ _ = _; apply congr_arg (adapter ..); change Ring.inverse _ * _ =B v 0 u0 _; rw [Ring.inverse_mul_cancel _ hu, show B v 0 u0=1 from hf.stone ..]; rfl
    exact ⟨(hh J).1.congr_of_eventuallyEq he,(hh J).2.1,fun n hn=> ((he.iteratedDeriv n).eq_of_nhds).trans ((hh J).2.2 n hn)⟩
omit hf hW hA
lemma fuel_by (p:ℂ)(w: F i u X Y): F i u (p • X) (p • Y):=by
    unfold Fuel; rw [draft_state]; refine ⟨w.unit,?_⟩; let A0:= Patria.Canvas.foil (A.density i); have hF:= Orientation.acting H 0 d (A0 (Wt i X)) Y.val w.sees p; change Beacon.ActionTest H 0 (A0 ⇑(p • setS A B i u X)) _; rw [show A0 ⇑(p • setS A B i u X)=p • A0 (Wt i X) from funext fun j=> mul_smul_comm p (Ring.inverse ((A.density i) j)) (setS A B i u X j)]; exact hF
lemma fuel_plus (x y:Label d)(h:F i u X Y)(hp:F i u x y):F i u (X+x) (Y+y):=by
    unfold Fuel; rw [draft_plus]; refine ⟨h.unit,?_⟩; let A0:= Patria.Canvas.foil (A.density i); change Beacon.ActionTest H 0 (A0 ⇑(setS A B i u X+ setS A B i u x)) _; rw [show A0 ⇑(setS A B i u X+ setS A B i u x)=A0 (Wt i X)+A0 (Wt i x) from funext fun i=>mul_add ..]; exact Orientation.actsPlus H 0 d _ _ _ _ h.sees hp.sees
abbrev chir(x: Label d):= sym.parity d x
lemma chi_twice: chir sym (chir sym X)=X:= by apply Subtype.ext; change (sym.parity d (sym.parity d X)).val=_; rw [sym.parityActs,sym.parityActs,UV.parity_twice]
def facing(p:Bool)(x:Label d) : Label d:= ((2:ℂ)⁻¹) • (if p then x - sym.parity d x else x+sym.parity d x)
lemma fronting (p:Bool):moored (facing sym p X).val p:=by
    let f:= sym.parity d; unfold moored; rw [← sym.parityActs]; change (f (facing sym p X)).val=_
    cases p
    · have h0:f (facing sym false X)=facing sym false X:=by unfold f facing; simp only [Bool.false_eq_true,↓reduceIte]; rw [map_smul,map_add,show sym.parity d (sym.parity d X)= _ from chi_twice sym X,add_comm]
      rw [h0]; exact (one_smul ℂ _).symm
    have h0:f (facing sym true X)=-(facing sym true X):=by unfold f facing; simp only [↓reduceIte]; rw [map_smul,map_sub (sym.parity d),show sym.parity d (sym.parity d X)=_ from chi_twice sym X]; exact (congr_arg (fun U:Label d=> ((2:ℂ)⁻¹) • U) (neg_sub X _).symm).trans (smul_neg ..)
    rw [h0]; exact (neg_one_smul ℂ _).symm
lemma revelation (x:Label d): x=facing sym true x+facing sym false x:=by
    unfold facing; simp only [Bool.false_eq_true,↓reduceIte]; rw [← smul_add,show x- sym.parity d x+(x+ sym.parity d x)= x+x by abel,← two_smul ℂ, inv_smul_smul₀ (by norm_num)] -- 2 Scalar 
include hf hW hA
lemma concordance :∃ y:Label d,F i u X y:=by
    have hp (v:Label d) (q:Bool)(h:moored v.val q) : ∃ y:Label d,F i u v y:=by
        by_cases hv:v=0; · rw [hv]; have h:= fuel_by A H B u _ _ 0 (bequeath A H sym B hf u hA W hW); rw [zero_smul] at h; exact ⟨_,h⟩
        obtain ⟨y,-,hh⟩:=arises_nonzero A H B u hA v W hW q hv h; exact ⟨y,hh⟩
    choose Y h using fun q=> hp (facing sym q X) q (fronting sym X q)
    nth_rw 1 [revelation sym X]; exact ⟨_,fuel_plus A H B u _ _ _ _ (h true) (h false)⟩
end Depth
end YM.Massive.Patria
#print axioms YM.Massive.Patria.Depth.concordance
