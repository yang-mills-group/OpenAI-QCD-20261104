import YM.QCD.Grove.Cry
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Trio.Sharp
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c C F L:Side}{w b j:ℕ}{B:BudgetPoint}{U V:Config G c}{t d p:ℝ}
lemma countD (w:ℕ)(o:Site c): separation o (delta w o)≤w:=by
    let p:Cover:= -(Slide.lev w)
    have hp:p∈Lattice.box w := Lattice.box_test.mpr ⟨fun i=> by simp [p,lev],fun i=> by simp [p,lev]⟩ -- no goals
    rw [show delta w o=wrap c p+o from ?_]; · exact Slide.sep p o hp
    unfold delta p; rw [map_neg]; abel
lemma beckon (t:ℝ)(w k:ℕ) (p:Site c) (H:w+b ≤ k) (U:Config G c)(hp:Healthy t (neighbors k p) U): Healthy t (neighbors b (delta w p)) U:=hp.mono_left fun i hi=>(neighbors_mem ..).2 ((separation_triangle p (delta w p) i).trans ((add_le_add (countD ..) ((neighbors_mem ..).1 hi)).trans H))
structure Isle (G:Gauge)(B: BudgetPoint)(w:ℕ)(c:Side)(Q s:ℝ):Prop where
   cipher : 2*(w+1)<c.val
   charts : 2*(2*w) ≤ c.val
   fruit (C:Side)(P:2*(2*w)≤ C.val)(p:Site C)(o:Site c) (U:Config G c)(h:Healthy B.threshold (neighbors (w+(2*w+1)) o) U): landscape B C Q s (shapeL P o p U)
   limits (P: Positions (Uniform.Primary c G))(h:‖P‖+2*Q<s)(hv:flags B.threshold (actual P)=∅): ∀ᶠ x in 𝓝[<] (1:ℝ), actual (x • P) ∈ Boulevard.sunny B
lemma spice (G:Gauge) (L:Side)(w:ℝ→ℕ)(hw:Rate G L 0 (fun i=>(w i:ℝ))) : ∀ᶠ x in atTop,∀ B:BudgetPoint, B.threshold=Pressure.temp x→ B.threshold ≤ 2*fiery G x L →∀ c:Side,2*(2*w x+1)< c.val → Isle G B (w x) c (furl G L x) (eaves G L x):=by
    let f x:= 2*w x+1
    have hf : Rate G L 0 (fun i=>(f i:ℝ)):= by unfold f; push_cast; exact (hw.mul_left 2).add (Rate.const _)
    obtain ⟨p,h,hp⟩:= expCost G 2 1; let r:=royalty G; have hr:0<r:= zero_lt_one.trans_le (royalty_ge G)
    let z x:= shade G*eaves G L x; have hx:Rate G L vow z:=(Sienna.edge G L).mul_left _
    let g x:=4*(sunLength p (z x)*r); have hg:Rate G L vow g:=((((hx.mul_left (1+1)).mul_left _).mul_right _).mul_left _)
    filter_upwards [hx.below vow_ok 1 zero_lt_one,Sienna.contraction G L (a:=r) (b:=r) hr (p:=vow*2) (hg.pow 2) (show vow*2 < -(1/2:ℝ) by norm_num [vow]), softly G L,Delay.shift_pos G L,Trio.pledges G L f hf] with x hx hX hZ hv he P ht hz c hw
    refine ⟨by omega,by omega,(fun C H p o U h=> carries _ _ (B:=P) (he P hz _ _ hw _ (show 2*w x+1 ≤ f x from le_rfl) H _ U (beckon (k:=w x+f x) _ _ _ le_rfl U h))),fun W hW hh=>?_⟩
    have hd:0<furl G L x:= Real.rpow_pos_of_pos hv _; have hΩ:‖W‖ < eaves G L x:= by linarith only [hd,hW]
    exact sunnySoon p (z x) hp W (mul_le_mul_of_nonneg_left hΩ.le (Uniform.shade_pos G).le) ((le_abs_self _).trans hx) hh (by change r*(g x)^2<P.threshold*r; refine hX.trans_le ?_; rw [mul_comm r,ht]; apply mul_le_mul_of_nonneg_right _ hr.le; rw [Real.rpow_neg hv.le]; exact hZ.2)
private lemma recolor (V:Config G c) (z:Site c→ G.El) (h:V∈Boulevard.sunny B): gauge z V∈Boulevard.sunny B:= fun i=> by rw [face_gauge,G.chord_conj]; exact h i
section wisdom
variable (hm:Isle G B w c p t) (x:Site c)(g:Config G c→ℝ)(hg:LocalOn (neighbors w x) g)
include hm hg
lemma threshold (l:List (Directions G c))(hl:l.length≤B.order)(hp:∀ U∈Boulevard.sunny B,‖leftDerivs g l U‖≤d)(U:Config G c)(he:Healthy B.threshold (neighbors (w+(2*w+1)) x) U)(ht:Push.Local.Chart B.order g U) : ‖leftDerivs g l U‖≤d:=by
    let V:= shapeL hm.charts x x U
    have hu:Agrees (neighbors w x) V U:= readNear x hm.cipher (hearth hm.charts x x _)
    have hK:∀ a:Directions G c, g (increment V a)= g (increment U a):=by intro a; refine hg _ _ (fun i h ht=> ?_); unfold increment; rw [hu i h ht]
    have hV: Push.Local.Chart B.order g V:=by unfold Push.Local.Chart; rw [show g ∘ increment V=g ∘ increment U from funext hK]; exact ht
    have hf:flags B.threshold V=∅:=flare _ x x U (he.mono_left (by intro i hi; exact (neighbors_mem ..).2 (((neighbors_mem ..).1 hi).trans (by omega))))
    obtain ⟨z,P,hP,h'⟩:=hm.fruit c hm.charts x x U he
    let F (t:ℝ):= gauge z⁻¹ (actual (t • P)); have hF:F 1=V:=by unfold F; rw [one_smul,hP]; funext i; simp only [Lattice.gauge,Pi.inv_apply]; group; rfl
    have hh i:ContDiffAt ℝ ω (fun t:ℝ=> G.mat (F t i)) 1:=by unfold F Lattice.gauge; simp only [G.mat_mul]; exact (contDiffAt_const.mul (radiator 1 P i)).mul contDiffAt_const
    have hx:Push.Local.Chart 0 (leftDerivs g l) (F 1):=hF.symm ▸ Next.Foundations.leftDerivs_chart _ _ (hV.of_le (by simpa using! Nat.cast_le (α:=WithTop ℕ∞)|>.mpr hl))
    have hy:leftDerivs g l U=leftDerivs g l (F 1):=by
       rw [hF]; -- via local induction
       suffices hz:∀ (U V:Config G c), Agrees (neighbors w x) V U →∀ l,leftDerivs g l U=leftDerivs g l V from hz _ _ hu l
       intro U V h l; induction l generalizing U V with
          | nil=> exact (hg _ _ h).symm
          | cons i l ih=> change deriv _ _=deriv _ _; apply congr_arg (fun V:ℝ→ℝ=>deriv V 0); funext k; exact ih _ _ (by intro j ht he; unfold increment; rw [h j ht he])
    rw [hy]; have hW: flags B.threshold (actual P)=∅:=by rw [hP,gauge_flags,hf]; -- term 
    have hh0:= (Push.Local.chart_comp hx hh).continuousAt.norm.tendsto.mono_left (show 𝓝[<] (1:ℝ)≤𝓝 1 from nhdsWithin_le_nhds)
    apply le_of_tendsto hh0; filter_upwards [hm.limits P h' hW] with a ha using hp _ (recolor _ _ ha)
end wisdom
end YM.PhysicalNext.Repeat.Trio.Sharp
