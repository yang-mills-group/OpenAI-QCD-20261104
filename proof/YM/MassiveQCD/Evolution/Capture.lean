import YM.MassiveQCD.Evolution.Floor
import YM.MassiveQCD.Evolution.Payment
import YM.MassiveQCD.Cabaret.PureGas
import YM.QCD.Kites.Bake
/-! # Coefficient stalls for forced receipts *after* e.g. Ruby merger.
 Includes all spin-post invoices under published exponent and `Metric.ball 0 (1/2)`,
 cost contraction to z in unit disk, and permits thereafter. No varying hits with poses
 when assembling coefficient budget in `Prize`.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Ruby
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Kites
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open MassiveQCD.Analysis.Shelf Metric
variable {c:Side}{N n B:ℕ}{t s r δ T τ u :ℝ}{i:Site c} {ι : Type}
local notation "Ω"=> EvenA c N

variable (p:Patron.Rail c N ι)
variable (Y:LanternK c N ι)
noncomputable def tokenC (t:ℝ):EvenA c N→L[ℂ] Grass.Alg (Keys c N):=LinearMap.toContinuousLinearMap ((Grass.changeVars (Matrix.diagonal (fun _=>(t:ℂ)))).comp (light (Keys c N))).toLinearMap
lemma tokenCC (t:ℝ)(x:Ω):token c N t x=tokenC t x:=rfl
noncomputable def dutyK (b: ℕ)(p:ι→ Cove.Hat c)(t v:ℝ)(x:Site c)(i:ι):ℝ:= if x∈ (p i).place then t^(p i).inv.card* Real.exp (v*coverNumber b (p i).place) else 0
lemma dutyQuit (f:ι→ℝ): Ac.Hit (home p) B (GasP.taxed (oriD p) f t) δ u↔∀ x,SumBudget (fun i=>dutyK B p.addr t δ x i*f i) u:=by
    apply forall_congr' fun x=>?_ ; suffices he: (fun i=>if x∈(p.addr i).place then GasP.taxed (oriD p) f t i *Real.exp (δ*coverNumber B (p.addr i).place) else 0)= fun i=>dutyK B p.addr t δ x i*f i from (by change SumBudget _ _ ↔ _; exact iff_of_eq (congr_arg (fun f=> SumBudget f u) he))
    funext i; unfold dutyK; split; next h=> exact mul_right_comm ..
    next h=> rw [zero_mul]
namespace LanternK
variable (Hq: Y.ChargedK u r t T B δ τ)(u':ℝ) (z:ℂ)
include Hq
lemma breaks (hv:0 ≤ u')(hh:u'≤1/4) : Quits (Y.phased u') B (4*u) τ δ t:=by
     let P x z:= Y.actsK z x
     let Q (i:ι)(j:Grid c) (z:ℂ):= tokenC t (P i z j)
     let a:= dutyK B Y.bud τ δ; have hf i x:0 ≤ a x i:= ite_nonneg (mul_nonneg (pow_nonneg Hq.system.le _) (Real.exp_pos _).le) le_rfl
     have he i j:Roof (Q i j):= fun z hz=> (ContinuousLinearMap.analyticAt (tokenC t (c:=c) (N:=N)) _).comp (Hq.aura i j z hz)
     have hx (i:ι):∃ x,0 < a x i:=by obtain ⟨x,hx⟩:=(Y.bud i).alive.mono (Y.bud i).part; exact ⟨_,by unfold a dutyK; rw [if_pos hx]; exact mul_pos (pow_pos Hq.system _) (Real.exp_pos _)⟩
     have hz x (hz:x∈sphere (0:ℂ) (1/2:ℝ))(F:ι→Grid c)(v:Site c): SumBudget (fun i=> a v i* ‖Q i (F i) x‖) u:=by
           have hx: x ∈ T':= mem_ball_zero_iff.mpr (lt_of_eq_of_lt (by simpa only [mem_sphere,dist_zero_right] using hz) (by norm_num))
           obtain ⟨f,h,hL⟩:= (Hq.power x hx).cost
           refine budget_mono ((dutyQuit (Y.get x) f).1 h v) (fun i=> mul_nonneg (hf _ _) (norm_nonneg _)) (fun i=> mul_le_mul_of_nonneg_left (hL _ (F i)) (hf i v))
     obtain ⟨f,hf,h⟩:= MassiveQCD.Analysis.Shelf.collection u u' (budget_nonneg (hz (1/2:ℂ) (by simp) (fun _=>1) 0)) hv hh Q a hf he hx hz
     refine ⟨f,(dutyQuit _ _).2 hf,?_⟩; rintro ⟨i,j⟩ V; rw [tokenCC]; change ‖tokenC t ((u':ℂ)^j • ampK (fun z=>Y.actsK z i V) j)‖ ≤ _; rw [map_smul,← projection j (fun z=>Y.actsK z i V) (Hq.aura i V 0 (by simp))]; exact h i j V
lemma speakeasy (i:ι)(V:Grid c)(hq:0≤u')(hr:u'<1)(he:‖z‖≤1): HasSum (fun n:ℕ=> z^n • (Y.phased u').warp (i,n) V) (Y.actsK (z*u') i V) :=by
     apply ((Hq.aura i V).expands (z*u') (by rw [norm_mul, Complex.norm_real,Real.norm_of_nonneg hq]; linarith only [mul_le_mul_of_nonneg_right he hq,hr])).congr_fun; intro n; simp only [mul_pow,mul_smul]; rfl
omit Hq
noncomputable def lampK (X:Patron.Rail c N ι)(p:ι→ℕ)(z:ℂ): Patron.Rail c N ι:=⟨X.addr,fun i=>(z^p i) • X.warp i⟩
lemma lampG (t:ℝ)(h:p.Reg t)(v:ι→ℕ): (lampK p v z).Reg t:=by
     refine ⟨fun i x y hx hy=> congr_arg (z^v i • ·) (h.uses i x y hx hy),fun i=>measurable_const.smul (h.reads i),?_,fun i V hP=> (h.buys i V (fun hh=>hP ((congr_arg (z^v i • ·) hh).trans (smul_zero ..))))⟩
     intro i V; unfold Gated lampK; dsimp only [Pi.smul_apply]; rw [map_smul]; exact Subalgebra.smul_mem _ (h.role ..) _ -- edit
lemma lampB (h: Quits p B u τ δ t)(hp':‖z‖≤1)(v:ι→ℕ): Quits (lampK p v z) B u τ δ t:=by
     obtain ⟨f,h,hf⟩:=h.cost; refine ⟨f,h,fun i V=>?_⟩; rw [tokenCC]; change ‖tokenC t (z^v i • _)‖≤ _; rw [map_smul,norm_smul,norm_pow]; exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hp')).trans (hf i V)
lemma lampInk (x:ℝ)(h:MixedInk p)(v:ι→ℕ)(hv:Tracks p v): MixedInk (lampK p v x):=by
   let M:=lampK p v (x:ℂ); have he i V: M.warp i V=x^v i • p.warp i V:=by change (x:ℂ)^v i • p.warp i V=_; rw [← Complex.ofReal_pow,Complex.coe_smul]
   constructor
   · intro i V z; apply congr_arg Subtype.val (show sways (Lat.rotates N z) (M.warp i _)=M.warp i V from ?_); rw [he,he,eSM _ (phare _)]; exact congr_arg _ (Subtype.ext (h.gauge i V z))
   · intro i V; change AccentFit (M.warp i V); rw [he]; exact AccentFit.dated _ _ (h.num i V)
   · intro i V; change Regal c N (M.warp i V) = M.warp i V; rw [he]; exact dolled _ _ (h.real ..)
   intro s z k hk; obtain ⟨e,h⟩:=hv.movesK s z k hk; exact ⟨e,fun i=>⟨(h i).2.1,(h i).2.2.1,fun V=>by unfold lampK; dsimp only [Pi.smul_apply]; rw [swayC,(h i).1,(h i).2.2.2]⟩⟩
end LanternK
end YM.QCD.Ruby
