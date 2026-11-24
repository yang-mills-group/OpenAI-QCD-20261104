import YM.QCD.Rain.Bowl
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Rain
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator InnerProductSpace
variable {c L:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ σ d A ε:ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Entr Kites Lunar Acre Rails Pressure ConnectedActivityE6 Cost Free Pine
open Jets.Touch Leaf LeafM Tee Eyrie Kites
open scoped ENNReal
noncomputable abbrev stG (c:Side)(t:ℝ): Set (Grid c):={V|‖TouchL‖ * ‖settled V-settled (1:Grid c)‖ < (c.val:ℝ)⁻¹ ∧∀ α:Face (Per c), su.chord (faceValue V α)<t}
lemma sparks (c:Side)(h:0<t): 1∈stG c t :=by
   refine ⟨by simp [Bloch.side_pos],fun α=>?_⟩; simp only [faceValue]; rw [show travel (1:Grid c) _ _=1 from ?_, Gauge.chord_one]; exact h -- name
   · simp [Lattice.travel,Lattice.square] -- Square ambiguous
lemma openness (c:Side)(t:ℝ): IsOpen (stG c t):=by
   apply IsOpen.inter
   · change IsOpen {V:Grid c | ‖TouchL‖ * ‖settled V-settled (1:Grid c)‖ < (c.val:ℝ)⁻¹}; apply isOpen_lt _ continuous_const; have hp:Continuous (settled:Grid c→ Pulse c):= by unfold settled Function.comp; fun_prop
     fun_prop
   change IsOpen {V:Grid c|∀ α:Face (Per c), su.chord (faceValue V α)<t}; simp only [Set.setOf_forall]; apply isOpen_iInter_of_finite; intro p; apply isOpen_lt _ continuous_const; unfold faceValue; fun_prop
lemma gardens (c:Side)(p:ℝ)(hp:0<p): 0 < (prior su c).real (stG c p):=by
     haveI:(prior su c).IsOpenPosMeasure:=by unfold prior; infer_instance
     exact ENNReal.toReal_pos ((openness ..).measure_pos (μ:=prior su c) ⟨1,sparks c hp⟩).ne' (measure_ne_top _ _)
lemma covers (V:Grid c)(p:BudgetPoint) (h:V∈stG c p.threshold): flags p.threshold V=∅:= Push.BetaTransport.flags_empty (fun α=> (h.2 α).le)
open Raft ParcelR WilsonStartup Fount
variable {Ω:ParcelR}
lemma forecast (f:Flavor N) (G:Plan j) (O:Clip)(L:Side)(δ H r η μ:ℝ)(hq:0<μ)(hp:Ω.Rates η)(l:ℕ):∀ᶠ x in atTop, let c:=sFirst L l (run L x); let t:=fiery su x L; ∃ P:ℝ,0<P ∧ 0 < (prior su c).real (stG c t) ∧ IsOpen (stG c t) ∧∀ (s:BudgetPoint),s.threshold=t → s.B=highR L x →∀ (v:PathData su)(M:Voice c N), v.Bounds O δ H r → Enn s f L x μ (1/8) (duo M.P M.K)→∀ A:SunR Ω,∀ T:YM.Next.Free.Train j,∀ V:Grid c,V∈stG c t → P ≤ (ber _ (Cove.light _ (red M.P M.K A G T s v O (haloK L x) (run L x) 0 0 V))).re:=by
     obtain ⟨D,hD,hE⟩:= snow; have hk:= (((basics L l).ruled.pow 4).mul (chip_rate L)).below (by norm_num) D hD
     filter_upwards [foliage G hp.hr hp.hs Ω.c Ω.d L N l μ hq,hk,event_chip L μ] with x hx hk hT c t
     obtain ⟨Y,hY⟩:= bPerf Ω hp O δ r H |run L x| c N -- order signature σ x P t yes
     have ht :0<t:=mul_pos (inv_pos.mpr (Real.sqrt_pos.2 hT.1)) (Delay.monitor_pos ..)
     let B:= G.μ/(c.val:ℝ)^2/2; have hb:0<B:=by unfold B; have hg:= G.price; positivity
     refine ⟨Real.exp (-Y) * (B^ Fintype.card (Modes c N)*(1/2)),by positivity,gardens c _ ht,openness c t,fun s hs hs' v M hv hM A T V hV=>?_⟩
     rw [←hs] at hV; have hf:= covers V s hV
     have h' (i:Grid c): 0 ≤ ‖(1:Sheet c)‖:=norm_nonneg _; let W:= FieldB Ω A c (haloK L x) G T+(0:ℝ) • 1
     have hu := panel f M hM hs' V; rw [site_card] at hu; push_cast at hu
     obtain ⟨hn,hW,hz,h⟩:=hx A.X A.Y T V 0 (by rw [abs_zero]; change 0 ≤ betaF su x L ^ _; have hx:=hT.1; positivity) hV.1.le
     let A0:= Finch.scent A.Z.page s v O (run L x) 0 N  (c:=c) -- arg syntax
     have hκ : wood G 0 T V+trunkM A.X A.Y (haloK L x) 0 (sFirst L l (run L x)) V= W V:=by unfold W FieldB trunkM; simp; rfl
     rw [hκ] at hn hW hz h
     apply le_trans _ (showers M V A0 W hf (fan_pos ..) _ hW.symm hn hz (hE _ _ _ (hu.trans ((le_abs_self _).trans hk)))) -- spaces
     have hh:= (abs_le.mp (hY A v s (run L x) hv le_rfl V)).1; apply mul_le_mul (Real.exp_monotone hh) (mul_le_mul_of_nonneg_right h (by positivity)) (by positivity) (Real.exp_pos _).le
end YM.QCD.Rain
