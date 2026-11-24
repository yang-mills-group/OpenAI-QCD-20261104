import YM.QCD.Globe.Miles
import YM.QCD.Nola.Wheat
import YM.QCD.Nola.Arch
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Globe
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden Entr Kites
variable {f c:Side}{j k m N:ℕ}{S:Flight j k} {h:f.val=c.val*S.L.val}{p:BudgetPoint}
open Nola
variable {a b t kT δ w Y:ℝ} {X: EvenA c N}{K:Sheet c}
lemma canopy (X: EvenA c N)(h: GrassA X t m a) (hx:0 < kT)(hf:0≤w)(ht:0 < t)(he:w*kT ≤ t): GrassA (wearK c N w X) kT m a:=by
     apply le_trans _ h; apply sum_le_sum; intro i _; unfold grainH; rw [show coef i (wearK c N w X).val=(w:ℂ)^i.card*coef i X.val from fundW ..,norm_mul,norm_pow, Complex.norm_real,Real.norm_of_nonneg hf];
     rw [mul_comm (w^_), mul_assoc ‖_‖, ← mul_pow]; gcongr; exact zero_le_one.trans (tell_one ..) -- inspect
lemma trueV (hp:Pure X)(w:ℝ): Pure (wearK c N w X):=by intro i hv; change coef i (engine w _ X.val) = _; rw [fundW, hp i hv,mul_zero]
-- exact pin budget
lemma counting (hp:Tempo K)(hc:sheen K=0): ∃ M: Sheet c,K=(mass K:ℂ) • (1:Sheet c)+M ∧ Drier M∧ Tempo M :=by
    let M:= K-(mass K:ℂ) • 1; have hh:Tempo M:=hp.sub (Tempo.one.smul _);
    refine ⟨M,?_,hh.staid ?_,hh⟩; · unfold M; abel
    intro i; unfold M; rw [map_sub,map_smul]; cases i
    · rw [show pina (0:Site c) none K = _ from (hp.night 0), CoatM, Option.elim_none,wavS,wave_one, show pina (0:Site c) none (1:Sheet c)=1 from coat1,sub_self]
    next i=> rw [show pina (0:Site c) (some i) K= _ from (hp.flange 0 i), show pina (0:Site c) (some i) (1:Sheet c)=0 from coatS i,hc,CoatM]; simp [wave]
noncomputable def dub (K M:Sheet c)(w:ℝ): Sheet c:= (w^2:ℝ) • (K+M)-K
noncomputable def dimeZ (V d:ℝ):ℝ:=4*d*V+2*d
lemma adjusts (K M:Sheet c)(w:ℝ)(he: w^2*(sheen K+sheen M)=sheen K)(hp:Tempo K)(hQ:Tempo M)(hv:Beam K 6 Y)(h:Beam M 6 δ)(hz:0≤ δ)(hY:0≤Y)(hh:w^2≤2)(hS:|w^2-1| ≤4*δ):
   let Z:= dub K M w
   Tempo Z∧ sheen Z=0 ∧ Beam Z 6 (dimeZ Y δ):=by
    intro Z; let q:=w^2; have ht:∀ v:ℝ,∀ X:Sheet c,v • X=(v:ℂ) • X:=fun _ _=>rfl
    have hZ : Tempo Z:= ((hp.add hQ).smul q).sub hp
    have hx:= hZ.flange 0 0
    let P:=pina (0:Site c) (some 0); change P Z= _ at hx
    refine ⟨hZ,?_,?_⟩
    · rw [show Z = (q:ℂ) • (K+M)-K from rfl,map_sub,map_smul,map_add,show P K= _ from hp.flange 0 0,show P M=_ from hQ.flange 0 0] at hx
      have hp(a:ℝ):CoatM (some 0) a=(a:ℂ) • (wave (Lat.gamma 0)):=wavS _ _
      have h: CoatM (some 0) (sheen Z)=0:=by change CoatM (some 0) (sheen ((q:ℂ) • (K+M)-K))=_; rw [← hx,hp,hp,← add_smul,smul_smul, ← Complex.ofReal_add, ← Complex.ofReal_mul, he]; simp
      exact abs_eq_zero.mp ((lesson_s _ _).trans (by rw [h,norm_zero]))
    have he₀: Z=(q-1:ℝ) • K+q • M:=by unfold Z dub q; rw [smul_add, sub_smul, one_smul]; abel
    rw [he₀,ht,ht]; apply Ton.up ((hv.smul (↑(q-1))).add (h.smul (q:ℂ))); rw [Complex.norm_real,Complex.norm_real,Real.norm_eq_abs, Real.norm_of_nonneg (sq_nonneg _)]; unfold dimeZ; exact add_le_add (mul_le_mul_of_nonneg_right hS hY) (mul_le_mul_of_nonneg_right hh hz)
lemma exactW {α θ:ℝ}(ht: 1/2 ≤ α)(hv:|θ|≤δ)(hp:δ ≤ 1/4):∃ w:ℝ, 1/2 ≤ w∧0<w∧w ≤2 ∧ w^2*(α+θ)= α ∧ w^2≤2 ∧ |w^2-1| ≤ 4*δ:=by
    have he : 1/4 ≤ α+θ:=by linarith only [ht,(abs_le.mp hv).1,hp]
    have hx: 0 < α+θ:=by linarith
    let x:= α/(α+θ); let w:=Real.sqrt x; have hX : 1/4≤x:= (le_div_iff₀ hx).mpr (by linarith only [ht,(abs_le.mp hv).2,hp]); have h0:x≤2:= (div_le_iff₀ hx).mpr (by linarith only [ht,(abs_le.mp hv).1,hp]); have h1:0<x:=by linarith
    have hW:0<w:=Real.sqrt_pos.mpr h1; have hz:w^2=x:=Real.sq_sqrt h1.le; refine ⟨w,by nlinarith, hW,by nlinarith,?_,hz.trans_le h0,?_⟩
    · rw [hz]; exact div_mul_cancel₀ _ hx.ne'
    rw [hz,show x-1= -θ/(α+θ) from ?_,abs_div,abs_neg, abs_of_pos hx, div_le_iff₀ hx]; · have hh := mul_le_mul_of_nonneg_left he ((abs_nonneg _).trans hv); linarith
    unfold x; field_simp; ring
structure Fused (X:EvenA c N) (K: Sheet c) (h r v:ℝ):Prop where
    tone:Tempo K
    rateG : sheen K=0
    remS : Beam (K-(mass K:ℂ) • 1) 6 r
    cocoa : Cocoa X
    moo  : Pure X
    work : GrassA X h 6 v
-- K full includes mass. separate cap.S κ
local notation "δ!"=> dimeZ Y δ
lemma lin (X: EvenA c N)(hp:Cocoa X)(he:Pure X)(hx:GrassA X (2*t) 6 a)(ht:0<t)(K M:Sheet c)(hK:Tempo K)(hM:Tempo M)(hv:Beam K 6 Y)(h:Beam M 6 δ)(hz:0≤δ)(hY:0≤ Y)(hf:1/2 ≤ sheen K)(hh:δ≤ 1/4): ∃ w:ℝ, let X':=wearK c N w X; let A:=dub K M w
    1/2 ≤ w∧0<w ∧ w≤2 ∧ wearK c N w (exp (paleF N (K+M)+X))=exp (paleF N (K+A)+X') ∧ |mass A|≤ δ!∧ Fused X' A t (2*dimeZ Y δ) a:=by
    have he' := (tone_bill (X:=M) h.toR hM (by decide)).2
    obtain ⟨w,hS,hV,hk,hq,hw,hz₀⟩:= exactW hf he' hh
    refine ⟨w,?_⟩; intro F A'; obtain ⟨hA,hA',hvA⟩:= adjusts K M w hq hK hM hv h hz hY hw hz₀; have ht' : |mass A'| ≤ dimeZ Y δ := (tone_bill hvA.toR hA (by decide)).1
    refine ⟨hS,hV,hk,?_,ht',⟨hA,hA', (hvA.sub (Ton.one.smul (mass A':ℂ))).up ?_,hp.beat _,trueV he _,canopy X hx ht hV.le (by positivity) (mul_le_mul_of_nonneg_right hk ht.le)⟩⟩
    · rw [map_exp (wearK c N w) (songT (N:=N) (c:=c) w).continuous,map_add,tastes]; rw [show K+A'=w^2 • (K+M) from ?_]
      unfold A' dub; abel
    simp only [Complex.norm_real,Real.norm_eq_abs,mul_one]; linarith
end YM.QCD.Globe
