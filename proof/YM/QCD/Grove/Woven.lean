import YM.QCD.Grove.Nick
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Grove
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun Kites
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.Frobenius
variable {I J V:Type}{c f:Side}{N n:ℕ}
open Animals
open Flume Orbit Quarry Folding Further.PhysicalPeriodLimitF933 Macrame PhysicalNext.Repeat Deck Meadow
open Pressure ConnectedActivityE6 Blaze King Push.Uniform
open Brick Dust Slide Trio.Sharp
-- layout
variable {C:Side}{D D' w j:ℕ}{d r t t' p p':ℝ}{B:BudgetPoint}
section scalar
variable (S:Gem c N I)(T:Finset I){b:ℝ}(hw:SoilB T S B w t')
set_option quotPrecheck false
local notation "V₀"=>primed T S
abbrev charge_v (B:BudgetPoint)(d:ℝ):ℝ:=2^B.order*(d+d)
include hw
lemma herring (hQ:∀ W:Positions (Push.Uniform.Primary c su), ‖W‖+2*p<p'→flags B.threshold (Boulevard.actual W)=∅→∀ l:List (Directions su c),l.length≤ B.order→(∀ i∈ l,‖i‖≤ B.threshold)→ ‖leftDerivs ((songT t' ∘ V₀)- (fun _=>Reggae.baker c N b)) l (Boulevard.actual W)‖≤d)(W:Positions (Push.Uniform.Primary c su))(hp:‖W‖+2*p<p')(hm:flags B.threshold (Boulevard.actual W)=∅)(l:List (Directions su c)) (hl:l.length≤ B.order)(he:∀ i∈ l,‖i‖≤ B.threshold): ‖leftDerivs (Boulevard.stillA (Trio.froth (crests (duskQ T S)))) l (Boulevard.actual W)‖ ≤ charge_v B d:=by
   let U:= Boulevard.actual W; let H: Grid c→EvenA c N:=(songT t' ∘ primed T S)- fun _=>Reggae.baker c N b
   let f:= Reggae.river c N ∘ H; let u:= Boulevard.stillA f
   have hv V (hx:flags B.threshold V=∅): Chart B.order H V:= ((songT (c:=c) (N:=N) t').contDiff.contDiffAt.comp 0 (mint T S hw V hx)).sub (f:=songT t' ∘ V₀ ∘ increment V) contDiffAt_const
   have hG (i:EvenA c N):‖Reggae.river c N i‖≤ ‖i‖:=by
      change ‖-(mud i).re‖≤ _; rw [norm_neg]; exact (Complex.abs_re_le_norm _).trans (Grass.piece_le _ _)
   have hf V (hx: flags B.threshold V=∅): Chart B.order f V:= (Reggae.river c N).contDiff.contDiffAt.comp 0 (hv V hx)
   have hu V (hx: flags B.threshold V=∅) : Chart B.order u V:= (hf V hx).sub (f:=f ∘ increment V) (show ContDiffAt ℝ _ (fun _ : Directions su c=> f 1) _ from contDiffAt_const)
   let K:= (Fintype.card (Strut c):ℝ)⁻¹; let Y i:= u ∘ Strut.sky i
   have h: Boulevard.stillA (Trio.froth (crests (duskQ T S)))=K • ∑ i, Y i:= clothS T S b t' -- order
   have hx : flags B.threshold (1:Grid c)=∅:=Boulevard.smoky (fun i=> by simpa [Gauge.chord,faceValue,square,travel,posDir,negDir,Lattice.Step.read] using B.threshold_pos) -- open
   have hv': (1:Grid c)= Boulevard.actual (0:Positions (Push.Uniform.Primary c su)):= by simp [Boulevard.actual]
   have heK:‖f 1‖ ≤d:=by
      rw [hv']; apply (hG _).trans; exact hQ 0 (lt_of_le_of_lt (add_le_add (norm_zero.le.trans (norm_nonneg W)) le_rfl) hp) (by rw [←hv',hx]) [] (by simp) (by simp)
   let F:= ∑ i,Y i; have hh i: flags B.threshold (Strut.sky i U)=∅:= Pane.tranquility _ hm _ _
   have hb i: Chart B.order (Y i) U:= chart_pull _ _ (hu _ (hh i)) -- K
   let M:ℝ→L[ℝ]ℝ:= K • ContinuousLinearMap.id ℝ ℝ; have hY : Chart B.order F U:=by
       unfold F; rw [show (∑ i,Y i)=(fun V=> ∑ i,Y i V) from funext fun i=> Finset.sum_apply ..]; exact ContDiffAt.sum (fun i _=> hb i)
   rw [show (Boulevard.stillA (Trio.froth (crests (duskQ T S))))= M ∘ F from h, left_linear M l hY hl]; unfold F; change ‖K* _‖ ≤ _; rw [norm_mul, Push.Local.left_sum _ _ _ _ (fun i _=> hb i) hl]
   refine le_trans (mul_le_mul_of_nonneg_left (norm_sum_le ..) (norm_nonneg _)) ((mul_le_mul_of_nonneg_left (sum_le_sum (g:=fun _=> charge_v B d) ?_) (norm_nonneg _)).trans_eq ?_)
   · intro i _; let s:= i.1; let x:=i.2; obtain ⟨P,hP,hM⟩:=Frost.parkL s x W; apply Frost.stall U s x (hu _ (hh i)) _ l hl he; intro j h hq
     rw [show u=f-(fun _:Grid c=> f 1) from rfl, AnalyticBridge.VerifiedReset.left_sub (g:=fun _=> f 1) (hf (pull s x U) (hh i)) (k:=B.order) contDiffAt_const h]; refine (norm_sub_le ..).trans (add_le_add ?_ ?_)
     · unfold U; rw [hM]; have hy:flags B.threshold (Boulevard.actual P)=∅:=hM ▸ (show flags _ (pull s x (Boulevard.actual W))=_ from hh i); unfold f; rw [left_linear (Reggae.river c N) j (hv _ hy) h]; exact (hG _).trans (hQ _ (lt_of_le_of_lt (add_le_add hP le_rfl) hp) hy j h hq)
     cases j; exact heK; rw [Work.G07.left_const]; rw [if_neg]; rw [norm_zero]; exact (norm_nonneg _).trans heK; simp -- def
   unfold K; rw [sum_const,nsmul_eq_mul, card_univ,norm_inv,Real.norm_of_nonneg (by positivity)]; field_simp
end scalar
end YM.QCD.Grove
#print axioms YM.QCD.Grove.herring
