import YM.QCD.Grove.Ship
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Grove
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun Kites
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J V:Type*}[Fintype I][Fintype J]{c f:Side}{N n:ℕ}
open Flume Orbit Quarry Folding Further.PhysicalPeriodLimitF933 Macrame PhysicalNext.Repeat Deck Meadow
open Pressure ConnectedActivityE6 Blaze King Push.Uniform
open Brick Dust Slide Trio.Sharp
-- layout
variable {C:Side}{D D' w j:ℕ}{d r t t' p p':ℝ}{B:BudgetPoint}
section orient
lemma sells (U: EvenA c N)(z:Frame c)(ht:0<t)(ht':0<t')(he:fareG 1 t N≤ t'):
   ‖token c N t ((orbitL (Lat.rotates N z)) U)‖≤ ‖token c N t' U‖:=by
     change load (fun _=>t) ((sways (Lat.rotates N z) U).val) ≤ load (fun _=>t') U.val; rw [← pendulum z]
     apply ferry _ _ _ _ (boarded U.val); · exact fun _=>ht'
     intro i _; have hf:= Dust.monument (o:=(0:Site c)) (ramp c z) i (Spice.holly z) ht; refine hf.1.trans ((le_trans ?_ he)); unfold fareG; have hi:0 ≤ stemF N:=by unfold stemF Jets.Sun.fingers; positivity
     nlinarith
lemma traceV (V:Grid c)(z: Frame c)(F:Grid c→ℝ)(l: List (Directions su c)): leftDerivs F (l.map (plume z)) (gauge z V)=leftDerivs (F∘ Lattice.gauge z) l V:=by
    induction l generalizing V with
    | nil=>rfl
    | cons a l ih=> simp only [RG.leftDerivs,List.map_cons]; apply congr_arg (fun V:ℝ→ℝ=>deriv V 0); funext t; rw [show increment (gauge z V) (t • plume z a)=gauge z (increment V (t • a)) from ?_]; exact ih _
                    funext i; unfold increment Lattice.gauge plume; simp only [Pi.smul_apply, ← map_smul,Channel.exp_adjoint]; group -- channel namespace
lemma recast (x:Site c)(f:Grid c→EvenA c N)(z:Frame c)(hv:shadeG f): shadeG (buds x N ∘ f):=by intro U k; exact congr_arg Subtype.val ((sought k (f (gauge k U)) x).trans (congr_arg _ (show sways (Lat.rotates N k) (f (gauge k U))= f U from Subtype.ext (hv ..)))) -- z unused
set_option maxHeartbeats 500000 in
lemma gild (V:Grid c)(f: Grid c→ EvenA c N)(b:ℝ)(p:Site c)(U: EvenA c N→L[ℝ]ℝ)(ht:0<t)(hT:0<t')(he: fareG 1 t N≤t')(hv:shadeG f)(hl: Trio.Sharp.landscape B c r p' V)(hp: flags B.threshold V=∅)(hM:∀ i,flags B.threshold i=∅→ Push.Local.Chart B.order f i)(hU : ∀ i,‖U i‖ ≤ ‖token c N t i‖) -- brushes
    (hQ:∀ W:Positions (Push.Uniform.Primary c su), ‖W‖+2*r<p'→flags B.threshold (Boulevard.actual W)=∅→∀ l:List (Directions su c),l.length≤ B.order→(∀ i∈ l,‖i‖≤ B.threshold)→ ‖leftDerivs ((songT t' ∘ f)- (fun _=>Reggae.baker c N b)) l (Boulevard.actual W)‖≤d)(l:List (Directions su c))(hh:l.length≤ B.order) (hs:∀ i∈l,‖i‖≤B.threshold):
     ‖leftDerivs (U ∘ buds p N ∘ f) l V‖ ≤ d:=by
   let Q:= buds p N ∘ f; obtain ⟨z,W,hW,h'⟩:=hl; let H:=gauge z V; let M:=orbitL (Lat.rotates N z); let K:=U.comp M
   have he': U ∘ Q=(K ∘ Q) ∘ Lattice.gauge z:=by
      funext i; change U (Q i)=K _; exact congr_arg U (show sways (Lat.rotates N z) _=Q i from Subtype.ext ((recast p f z hv) i z)).symm
   let v:=l.map (plume z); have hz: v.length ≤ B.order:=by unfold v; simpa
   have hs':∀ i∈v,‖i‖≤ B.threshold:=by
      intro i hi; obtain ⟨i,h0,rfl⟩:= List.mem_map.mp hi; apply (pi_norm_le_iff_of_nonneg B.threshold_pos.le).2; intro k; unfold plume; rw [su.norm_adjoint]; exact (norm_le_pi_norm _ _).trans (hs _ h0)
   have hX : flags B.threshold H=∅:=by unfold H; rw [gauge_flags,hp]
   -- term X=baker offset. acts through U annihilates. use CLM on X before expected.t'
   let J:=songT (c:=c) (N:=N) (t'⁻¹); let G:= K.comp ((buds p N).comp J); let F:Grid c→ EvenA c N:= (songT t' ∘ f)- (fun _=> Reggae.baker c N b)
   have hK: K ∘ Q= G ∘ F:=by
      funext i; change K _= K (buds p N (wearK c N (t'⁻¹) (wearK c N t' (f i) - Reggae.baker c N b))); rw [map_sub,wit (f i) (t'⁻¹) t' (inv_mul_cancel₀ hT.ne'), juke,map_sub, scalesR,sub_zero]; rfl
   change ‖leftDerivs (U ∘ Q) l V‖≤ d; rw [he',← traceV V z (K ∘ Q), hK, left_linear _ _ (show Push.Local.Chart B.order F H from ((songT (c:=c) (N:=N) t').contDiff.contDiffAt.comp 0 (hM _ hX)).sub (f:=songT (c:=c) (N:=N) t' ∘ f ∘ increment H) contDiffAt_const) hz]
   let X:=leftDerivs F v H; change ‖G X‖≤ d; refine (hU (M _)).trans ((sells (buds p N (J X)) z ht hT he).trans ((corporation p _ t' hT).trans ?_))
   rw [skill,show wearK _ _ _ (J X)=X from wit _ _ _ (mul_inv_cancel₀ hT.ne')]
   unfold X H; exact hW ▸ (hQ W h' (by rw [hW]; exact hX) v hz hs') -- Eq rewrite
end orient
end YM.QCD.Grove
