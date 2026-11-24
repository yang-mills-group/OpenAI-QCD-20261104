import YM.MassiveQCD.Palette.Flash
import YM.MassiveQCD.Palette.Shapes
/-! # Payments for pointed flavor rays, simultaneous in the Π-F norm -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stew.Phased
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Port Jets Jets.Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N n:ℕ} {t u T C:ℝ} {o:Site c}{p:BudgetPoint}
open Revolve Flume Quarry AnalyticBridge.VerifiedReset Footprint
lemma beams (a:ℝ)(ha:0<a)(f:Flavor N→ Spike) {o:Site c}: Sen o a (beam o f)≤a^2*(fingers N)^2 *‖goldW‖ * ‖f‖:=by
    let o':= o; let v:=beam o f; let X:=Matrix.blockDiagonal (fun i=>localX o (f i)); have hx := flashPad f (mem_singleton_self o)
    let w i j:= if (i=o ∧ j=o) then ‖goldW‖ * ‖f‖ else 0; have he i j:0 ≤ w i j := ite_nonneg (by positivity) le_rfl
    have h i j: ‖X i j‖≤ w (headF i) (headF j):=by
       unfold X; rw [Matrix.blockDiagonal_apply]; split
       next hm=>
         have hx a b: cell (localX o (f i.2)) a b=if a=o ∧ b=o then wave (f i.2) else 0:=by rw [siteBl,pairBl]
         change ‖cell (localX o (f i.2)) i.1.1 j.1.1 i.1.2 j.1.2‖ ≤ if (i.1.1=o∧j.1.1=o) then _ else _; rw [hx]; split
         · exact (Cost.north _ _ _).trans ((goldW.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm f i.2) (norm_nonneg _)))
         rw [Matrix.zero_apply,norm_zero]
       rw [norm_zero]; exact he _ _
    have hp: (∑ i:Site c,∑ j,w i j)=‖goldW‖ * ‖f‖:=by 
         unfold w
         rw [sum_eq_single o]; · simp
         · intro i hi hk; simp [hk]
         simp
    apply (senCamp {o} (n:=0) (by intro x hx; rw [mem_singleton.mp hx]; simp) _ ha hx).trans; apply le_trans (mul_le_mul_of_nonneg_left (fauna X ha) (sq_nonneg _))
    have hh:= paddleB (F:=N) 0 (∅:Support c) 0 (fun i j=> ‖X i j‖) w h; rw [hp] at hh
    simp only [Nat.cast_zero, add_zero, one_pow, one_mul, jacket]; exact (mul_le_mul_of_nonneg_left hh (sq_nonneg _)).trans_eq (by ring)
lemma constChoice (o:Site c)(V:EvenA c N)(r A:ℝ) (U:Support c)(P:BudgetPoint)(h: Sen o A V ≤ r) (hg:Gated U V): Woven o U P A (fun _=> V) r:=by
    have hr:= (norm_nonneg _).trans h; refine ⟨fun _ _ _=> rfl, fun _=>hg, fun _ _=>contDiffAt_const, fun _ _ l _ _=>?_,measurable_const,hr⟩
    cases l with
    | nil => exact h
    | cons i l=> rw [show leftDerivs _ _ _=(0:EvenA c N) from (Work.G07.left_const V (i::l) _),← measures,map_zero,norm_zero]; exact hr
noncomputable def stampFee (N:ℕ):ℝ:=1+(fingers N)^2 * ‖goldW‖ -- not same as QuintP per-Origin
lemma stampFound :1≤ stampFee N:= le_add_of_nonneg_right (by positivity)
lemma stamped (o:Site c)(h:0<t)(f:Flavor N→Spike)(P:BudgetPoint): Woven o {o} P t (fun _=>beam o f) (stampFee N*(t^2*‖f‖)):= by
    refine constChoice o _ _ _ _ P ((beams t h f).trans ?_) (flashPad f (mem_singleton_self _))
    unfold stampFee; nlinarith only [mul_nonneg (sq_nonneg t) (norm_nonneg f)]
lemma wage (M:Flavor N→ ℝ): ‖fun i:Flavor N=> (M i:ℂ) • (1:Spike)‖=‖M‖:= by
      have H(x:ℝ): ‖(x:ℂ) • (1:Spike)‖=‖x‖:=by rw [norm_smul,norm_one,Complex.norm_real,mul_one]
      exact le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i=> (H _).le.trans (norm_le_pi_norm M i))
        ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i=> (H _).symm.le.trans (norm_le_pi_norm (fun i=>(M i:ℂ) • (1:Spike)) i))
variable {ι:Type}(E:Gem c N ι) {w:ι→ℝ}
lemma postK (hp:0 ≤ u)(hv:∀ (c:Side) (N:ℕ)(b:Flavor N)(i: Site c)(X:EvenA c N)(j: SampleX)(w:ℝ), 0 ≤ w→ w^2 * ‖shape i (feeF b X) j‖ ≤ u*Sen i w X) (t:ℝ)(ht:0 < t)(i:ι)(hh:Woven (E.addr i).site (E.addr i).support p t (E.view i) C) : t^2*‖fun b:Flavor N=> lane E b i none‖ ≤ u*C:=by
    have hm: t^2>0:=by positivity
    rw [mul_comm (t^2), ← le_div_iff₀ hm]; refine (pi_norm_le_iff_of_nonneg (div_nonneg (mul_nonneg hp hh.travel) hm.le)).2 ?_
    intro b; rw [le_div_iff₀ hm,mul_comm _ (t^2)]; unfold lane mote; split
    · apply (hv c N b _ _ _ _ ht.le).trans; exact mul_le_mul_of_nonneg_left (hh.sizeU _ (flat_ok ..)) hp
    rw [norm_zero,mul_zero]; exact mul_nonneg hp hh.travel
lemma rayTicket (C:ℝ)(hp:1≤u)(h:∀ (c:Side) (N:ℕ)(b:Flavor N)(i: Site c)(X:EvenA c N)(j: SampleX)(w:ℝ), 0 ≤ w→ w^2 * ‖shape i (feeF b X) j‖ ≤ u*Sen i w X)(hU:Licence p T C t E)(ht:0<t)(hz :0 ≤ T) : t^2*‖fun i:Flavor N=> qMass (till E i o)‖ ≤ u*C:=by
    obtain ⟨f,hF,hS⟩:= hU.zone
    have hK : t^2>0:=by positivity
    have hC :0≤ C:=budget_nonneg (hF o)
    rw [mul_comm (t^2),← le_div_iff₀ hK]; apply (pi_norm_le_iff_of_nonneg (show (0:ℝ)≤u*C/t^2 from by positivity)).mpr; intro i; rw [le_div_iff₀ hK, Real.norm_eq_abs,mul_comm _ (t^2)]; exact (mul_le_mul_of_nonneg_left (crops ..).1 hK.le).trans (Stew.diligent E i hF hS ht hz hp h none o)
end YM.QCD.Stew.Phased
