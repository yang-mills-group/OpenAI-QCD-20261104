import YM.QCD.Stew.Expense
/-! # Slopes & bounded exact projection with leases. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stew
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N n z B D:ℕ} {w r a u t σ η A' K Q' y:ℝ}{p:BudgetPoint}{o:Site c}
open Revolve Flume Quarry AnalyticBridge.VerifiedReset Port Footprint
variable {ι:Type}(E:Gem c N ι)(b:Flavor N)
open Residual
-- keep signs frequent. Can use Scalar projection Local externally. Carry h.direction E budget together. PreArea gen parameter.
structure Licence (p:BudgetPoint)(Z z K:ℝ)(E:Gem c N ι) :Prop where
 zone : ∃ f:ι→ℝ,Anchored (fun i=>(E.addr i).site) f (fun i=>coverNumber p.B (E.addr i).support) Z z ∧ ∀ i, Woven (E.addr i).site (E.addr i).support p K (E.view i) (f i)
structure Purchases (Y:Ruby.Hue c N ι)(t:ℝ)(B:ℕ)(a K p:ℝ):Prop where
 projection : Y.Garish
 life : Y.Tall t
 paint : ∃ f:ι→ℝ,(∀ i U,‖token c N p (Y.mean i U)‖ ≤ f i) ∧Ac.Hit Y.bud B f a K
variable {f:ι→ℝ} (h: Anchored (fun i=>(E.addr i).site) f (fun i=> coverNumber p.B (E.addr i).support) σ a) (hp:∀ i,Woven (E.addr i).site (E.addr i).support p u (E.view i) (f i))
include h hp
lemma cumulative (C:ℝ)(hs:0≤σ)(hc:0≤C)(hk:2 ≤ p.B)(he:0 ≤ t)(hZ:t+1+1≤σ):
   let X:=lien E b p.threshold; let B:=dearth E b
   Anchored (fun i=>(B.addr i).site) (fun i=>C*f i) (fun i=> coverNumber p.B (B.addr i).support) σ (C*Real.exp (81*σ)*a) ∧Ac.Hit X.bud p.B (fun i=> C*f i) t (Footprint.payment 1 (4*p.B+2) 0 1 C a t 81):=by
    intro X B; have ht i:= (hp i).travel; have hh i:(coverNumber p.B (way (E.addr i)):ℝ)≤ coverNumber p.B (E.addr i).support+81:= by
       have he: coverNumber p.B (way (E.addr i))≤ coverNumber p.B (E.addr i).support+81:= Geo.enlarge p _ hk
       exact_mod_cast he
    constructor
    · intro x; apply budget_mono (budget_scale (mul_nonneg hc (Real.exp_pos _).le) (h x))
      · intro i; split; exact mul_nonneg (mul_nonneg hc (ht _)) (Real.exp_pos _).le; exact le_rfl
      intro i; by_cases hv : (E.addr i).site=x
      · rw [if_pos (show (B.addr i).site=x from hv),if_pos hv]; dsimp only []; rw [← mul_assoc (C*_), mul_assoc C _ (f i), mul_comm (Real.exp _) (f _),← mul_assoc, mul_assoc (C*_),← Real.exp_add] -- edit
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hc (ht _)); apply Real.exp_monotone; apply (mul_le_mul_of_nonneg_left (hh i) hs).trans; linarith
      rw [if_neg hv, mul_zero, if_neg (show ¬ (B.addr i).site=x from hv)] -- defeq
    exact Footprint.assigned id 1 (fun Y : Support c=> by simp) _ _ ht _ _ h _ 0 _ (fun i x hx=> Geo.enlarged_dist p (E.addr i) x hx) (fun i=> by rw [one_mul,add_comm]; exact hh i) hc ⟨he,by norm_num,by linarith⟩ _ (fun i=> mul_nonneg hc (ht i)) (by simp)
lemma diligent (hj:0<u)(ht:0≤σ) (hv:1 ≤ K)(hK: ∀ (c:Side) (N:ℕ)(b:Flavor N)(i:Site c)(X:EvenA c N)(j)(w:ℝ),0 ≤ w → w^2*‖shape i (feeF b X) j‖ ≤ K*Sen i w X)(p':SampleX)(z:Site c): u^2*‖till E b z p'‖≤ K*a :=by
    have hU:=sq_pos_of_pos hj; let Y:=unitM E b z p'
    have he : SumBudget (fun i=> u^2 * ‖Y i‖) (K*a):=by
       apply budget_mono (budget_scale (zero_le_one.trans hv) (h z)) (fun _=> by positivity); intro i; split
       next hg=> unfold Y unitM lane mote; rw [if_pos hg.symm]; split
                 next ht'=> apply (hK _ N b _ _ _ _ hj.le).trans; apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hv); exact ((hp i).sizeU 1 (flat_ok ..)).trans (le_mul_of_one_le_right (hp i).travel (Real.one_le_exp (mul_nonneg ht (by positivity))))
                 next H=> rw [norm_zero, mul_zero]; have hp:0 ≤ f i:= (hp i).travel; positivity
       next hv=> unfold Y unitM; rw [if_neg (mt Eq.symm hv), norm_zero,mul_zero,mul_zero]
    have hg : Summable fun i=> ‖Y i‖:= by
       apply (he.2.1.mul_left (u^2)⁻¹).congr; intro i; exact inv_mul_cancel_left₀ hU.ne' _
    exact (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hg) hU.le).trans (by rw [← hg.tsum_mul_left]; exact he.2.2)
lemma readsV (hc:Crossing E)(hs:0≤σ)(ht:0<u) (V:Grid c) : HasSum (fun i=>(lien E b p.threshold).mean i V+letters (dearth E b) p.threshold V i) ((Patron.total E p.threshold V)- paleF N (backP (till E b 0) V)):=by
    let T:= lien E b p.threshold; let X:= mintF E b V; have hQ :Summable f:= Loom.sumRide _ _ _ h (fun i=>(hp i).travel) hs
    have he:E.Gather:=⟨fun i=>(hp i).room,fun i=>(hp i).Borel,fun i=>(hp i).gated⟩; have ht':= everP E b he hc (fun i=>costsE E b hQ ht (fun i=>(hp i).sizeU 1 (flat_ok ..)) _) V
    let L i:=letters E p.threshold V i; have hh i: ‖Fleet.songT u (L i)‖ ≤ f i:=by
       have hv :(‖songT u (L i)‖)= ‖token c N u (L i)‖:=rfl
       rw [hv]; unfold L letters; by_cases h': Healthy p.threshold (E.addr i).support V; · rw [masked_eq _ _ _ _ h']; exact (shot (lens _) _ _ ht).trans ((hp i).sizeU V h')
       rw [masked_ne _ _ _ _ h',map_zero,norm_zero]; exact (hp i).travel
    have hw : Summable L:=by apply ((songT u⁻¹).summable (Summable.of_norm_bounded hQ hh)).congr; intro i; exact wit (L i) _ _ (inv_mul_cancel₀ ht.ne')
    apply (hw.hasSum.sub ht').congr_fun; intro i; change L i-(_ + X i)+ _=L i-_; abel -- ambiguity
end YM.QCD.Stew
