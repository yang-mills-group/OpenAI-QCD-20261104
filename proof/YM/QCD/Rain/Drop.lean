import YM.QCD.Rain.Flips
import YM.QCD.Hearth.Tower
/-!
# small-physical side budget: Wick.Price even and Grass partition
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Rain
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c L:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ σ d A ε:ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Entr Kites Lunar Acre Rails Pressure ConnectedActivityE6
variable {ι β:Type} (b:Flavor N)
lemma panel (K:Voice c N) (hp:Enn p b L t η a (duo K.P K.K)) (h: p.B=radiusB (run L t)) (W:Grid c) :
      ‖wearK c N (Jets.Touch.fan L η t) (Patron.total K.P p.threshold W)‖ ≤ (Fintype.card (Site c):ℝ)* Jets.Touch.chip L t :=by
    let Y:=duo K.P K.K; obtain ⟨f,g,hK,hZ⟩:= hp; let s:=Jets.Touch.fan L η t; have he:s>0:=Jets.Touch.fan_pos ..
    have hm(k:K.ι):=hK.centsP.pos k; have hh:= hK.fillP.χ; have hh0: p.B=Jets.Touch.highR L t:=h; rw [← hh0] at hh; have ht:=Stem.mast K.P f (B:=p) hh hm hK.fillP.bud
    let U:=letters K.P p.threshold W; have hx(k:K.ι): ‖songT s (U k)‖ ≤ f k:=hK.centsP.cost k W
    have hu:= Summable.of_nonneg_of_le (fun _=>norm_nonneg _) hx ht.2.1; have hs : Summable U:=by
        apply ((songT s⁻¹).summable hu.of_norm).congr; intro j; exact wit (U j) _ _ (inv_mul_cancel₀ he.ne')
    change ‖songT s (∑' i,U i)‖≤_; rw [← ((songT s).hasSum hs.hasSum).tsum_eq]; exact (norm_tsum_le_tsum_norm hu).trans ((Summable.tsum_le_tsum hx hu ht.2.1).trans ht.2.2)
lemma snow :∃ d:ℝ,0<d∧∀ c:Side,∀ N:ℕ,∀ x:EvenA c N, ‖x‖≤d→ ‖exp x-1‖≤1/2:=by
    let f (x:ℝ):=x^2*Oasis.mercyK+x
    have hf:∀ᶠ x in 𝓝[>] (0:ℝ), f x≤1/2∧x≤1 :=by
       have hp:(f 0)<1/2:=by unfold f; norm_num
       have h:Continuous f:=by unfold f; fun_prop
       refine mem_nhdsWithin_of_mem_nhds ((?_ :∀ᶠ x in 𝓝 (0:ℝ), f x≤1/2).and (eventually_le_nhds zero_lt_one)); exact (h.tendsto _).eventually_le_const hp -- typo
    obtain ⟨d,⟨h,he⟩,hd⟩:= (hf.and self_mem_nhdsWithin).exists; have hh:0<d:=hd
    refine ⟨d,hh,fun c N x hx=>?_⟩; have hz := Oasis.mercy (h:=x) (show ‖x‖≤2*d by linarith only [hx,hh]) hh he
    unfold f at h; exact (norm_le_norm_add_norm_sub' (exp x-1) x).trans (by linarith only [hz,h,hx]) -- check lemma style
lemma showers (K:Voice c N) (X:Grid c)(G:Grid c→ℝ) (W:St c) (hb:flags p.threshold X=∅) (hp:0<w) (θ:ℝ) (h:(Lat.copies N (W X)).det = (θ:ℂ)) (hd:0<θ) (hv: ‖(Lat.copies N (W X))⁻¹‖≤w^2) (hK:‖exp (wearK c N w (Patron.total K.P p.threshold X))-1‖ ≤1/2) :
      Real.exp (G X) * (θ* (1/2)) ≤ (ber _ (Cove.light _ (scoreV K.P K.K p.threshold G W X))).re:=by
     let d:=G X; let M:= Lat.copies N (W X); have hz:0<Real.exp d:=Real.exp_pos _; have hm : IsUnit M.det:=isUnit_iff_ne_zero.mpr (show M.det≠0 from h.symm ▸ (by exact_mod_cast hd.ne'))
     let Y:=Cove.light _ (exp (Patron.total K.P p.threshold X))
     have hvY := Rails.poem K.P K.K W X G (β:=p.threshold);
     have he : (duo K.P K.K).bluff p.threshold X = Y:=by unfold Rise.bluff Y; rw [(Rails.heart K.P K.K X).1,(Rails.heart K.P K.K X).2, High.PrismT.bank K.K _ _ hb, mul_one] -- depends params.
     rw [hvY,he]; change Real.exp d*_≤_; let q:= seen M; have hσ:q (Y-1)=q Y-1:=by rw [map_sub,seen_one hm]
     have hA: load (fun _=>w) (Y-1)≤ 1/2:=by
         have he: exp (wearK c N w (Patron.total K.P p.threshold X))-1=wearK c N w (exp (Patron.total K.P p.threshold X)-1):=by rw [map_sub,map_one, map_exp (wearK c N w) (songT w).continuous]; -- orientation
         rw [he] at hK; rw [show Y-1=Cove.light _ (exp (Patron.total K.P p.threshold X)-1) from ((Cove.light (Keys c N)).map_sub ..|>.trans ?_).symm]; · exact hK
         rw [map_one]; rfl
     have h1: 1/2 ≤ (q Y).re:=by
         have he: ‖q (Y-1)‖≤1/2 :=(seeing _ hm hp hv (Y-1)).trans hA
         have hh:= (abs_le.mp ((Complex.abs_re_le_norm (q (Y-1))).trans he)).1; rw [hσ] at hh; simp only [Complex.sub_re, Complex.one_re] at hh; linarith
     have hU : ber _ (gauss M * Y) = (θ:ℂ)*q Y:=by rw [← h]; change _= M.det * seen M _; rw [seen_apply,mul_inv_cancel_left₀ hm.ne_zero]
     -- scalar map
     let v:= (ber (Modes c N)).restrictScalars ℝ
     change _≤ (ber _ (((Real.exp d:ℝ):ℂ) • (gauss M*Y))).re -- Real.exp syntax
     rw [map_smul, hU, smul_eq_mul]; simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]; gcongr
end YM.QCD.Rain
